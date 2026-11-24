#include "higher_machine.h"
#include "term.h"
#include "native_memory.h"
#include "native_vector.h"

#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include <stdatomic.h>

#define NONE SIZE_MAX
#define MAGIC INT64_C(0x484f4c31)
#define BATCH 4096

typedef struct {
    HTerm goal;
    size_t next, scope, hyps, barrier;
    uint64_t premises, call;
} Frame;

/* Each chain version owns a persistent predicate map. Unknown heads have
    * their own key and are merged with a rigid key in original source order. */
typedef struct {
    HTerm fact, rigid_head;
    size_t next, index_root, same, index_end;
    /* This fact, or an older one of its chain, is no clause. */
    int unusable;
    /* One more than the newest fact of this chain, this one included, that is
        * a clause or not according to a variable that was unbound when it came;
        * 0 when the chain has none. A search looks at those again. */
    size_t undecided;
} Hypothesis;
typedef struct { uint64_t identity; unsigned kind; } HypKey;
typedef struct {
    size_t bit;
    union { size_t children[2]; struct { HypKey key; size_t value; } leaf; } value;
} HypIndex;
/* next: the following fact of the same predicate, or of the dynamic facts.
    * peer: the following fact with the same first-argument key, or, for a fact
    * without a key, the following fact of the predicate without a key.
    * rigid is the head constant of a fact that has the literal clause shape and
    * a rigid head; head, body, binders and arity then describe that shape. No
    * binding reaches it, so it is read once, when the fact is loaded. */
typedef struct { int64_t symbol; HTerm fact; size_t next, peer; HTerm head, body, rigid; size_t binders, arity; uint64_t clash_args; uint32_t type_binders; } Fact;
typedef struct { size_t first, last, plain_first, plain_last, arity; unsigned char kinds, mixed; } Predicate;
/* literal == HT_NONE: key is a constant symbol; otherwise literal supplies
    * the canonical decimal digits. The persistent index uses their full bytes. */
typedef struct { size_t symbol, key; HTerm literal; size_t first, last; } Bucket;
typedef struct BucketIndex {
    _Atomic size_t references;
    size_t bit, bytes;
    struct BucketIndex *drop_next;
    union {
        struct BucketIndex *children[2];
        size_t bucket;
    } value;
} BucketIndex;

static void index_retain(BucketIndex *node)
{
    if (node) atomic_fetch_add_explicit(&node->references, 1, memory_order_relaxed);
}

/* No C recursion, including a trie of very long natural-literal keys. Only
    * a node whose last reference was released may use its private drop link. */
static void index_release(BucketIndex *node)
{
    if (!node || atomic_fetch_sub_explicit(&node->references, 1, memory_order_acq_rel) != 1) return;
    node->drop_next = NULL;
    while (node) {
        BucketIndex *next = node->drop_next;
        if (node->bit != SIZE_MAX) for (size_t i = 0; i < 2; ++i) {
            BucketIndex *child = node->value.children[i];
            if (child && atomic_fetch_sub_explicit(&child->references, 1, memory_order_acq_rel) == 1) {
                child->drop_next = next;
                next = child;
            }
        }
        hm_free(node);
        node = next;
    }
}

typedef struct { int kind; size_t symbol; HTerm literal; } Key;
typedef struct { size_t stamp; HTerm head; } StringPrefix;
/* The buffers of the string literals of one wordcode fragment, by the place of
    * their elements in its payload and by their constructors. */
typedef struct { size_t offset, length, cons, nil, type; HTStringBuffer *buffer; } StringLiteral;
typedef struct {
    StringLiteral *literals;
    size_t count, capacity;
    StringPrefix *prefixes;
} StringCache;
/* A persistent assignment holds wherever its target exists. state says what
    * the store has of it: ASSIGNMENT_MADE, the binding is there at every
    * checkpoint that is not older than (trail, heap), the sizes of the trail and
    * of the heap just after it was made; ASSIGNMENT_GONE, the target did not
    * exist when it was last looked up; ASSIGNMENT_OPEN, it is to be made. */
enum { ASSIGNMENT_OPEN, ASSIGNMENT_MADE, ASSIGNMENT_GONE };
typedef struct { uint64_t target; int64_t *wire; size_t length, trail, heap; int state; } Assignment;
typedef struct {
    HTCheckpoint terms;
    size_t work, hyps;
    uint64_t host, view;
    size_t view_trail;
} Checkpoint;
typedef struct {
    uint64_t token;
    BucketIndex *set;
    size_t count;
    int kind, live;
} HostRoots;
typedef struct {
    HTerm goal, head;
    size_t arity, global, keyed, unkeyed, dynamic, local, local_unknown, barrier;
    Frame frame;
    int phase, fallback, equality, plain, local_indexed;
} Search;
typedef struct {
    int kind;
    uint64_t serial;
    Checkpoint checkpoint;
    size_t work_head;
    Search search;
} Choice;

enum { ACTION_NEXT, ACTION_EXECUTE, ACTION_SEARCH, ACTION_FAIL, ACTION_ANSWER };
enum { CONTINUE_WORK, CONTINUE_IMPLY, CONTINUE_EQUALITY, CONTINUE_DEBUG, CONTINUE_ANSWER, CONTINUE_ACTION };
enum { SEARCH_GLOBAL, SEARCH_LOCAL, SEARCH_EQUAL_LOCAL, SEARCH_EQUAL_GLOBAL };
enum { KEY_NONE, KEY_NATURAL, KEY_CONSTANT, KEY_NOMINAL };
enum { LOAD_CREATE, LOAD_EXTEND, LOAD_QUERY };

enum { TABLE_ROLES, TABLE_FACTS, TABLE_PREDICATES, TABLE_BUCKETS, TABLE_COUNT };

typedef struct ProgramVersion {
    _Atomic size_t references;
    struct ProgramVersion *parent;
    size_t bytes;
} ProgramVersion;

static void retain_version(ProgramVersion *version)
{
    if (version) atomic_fetch_add_explicit(&version->references, 1, memory_order_relaxed);
}

static void release_version(ProgramVersion *version)
{
    while (version && atomic_fetch_sub_explicit(&version->references, 1, memory_order_acq_rel) == 1) {
        ProgramVersion *parent = version->parent;
        hm_free(version);
        version = parent;
    }
}

struct HolV2Machine {
    HMemory *memory;
    int error_code, api_code, legacy_copy;
    HvVector program[TABLE_COUNT];
    HMemoryLease *table_leases[TABLE_COUNT];
    ProgramVersion *version;
    HMemoryLease *version_lease;
    uint64_t engine_origin;
    HolTermStore *terms;
    size_t symbol_count, meta_count;
    size_t fact_count, dynamic_first, dynamic_last;
    size_t predicate_count;
    size_t bucket_count;
    BucketIndex *bucket_index;
    HMemoryLease *index_lease;
    size_t program_symbols, program_meta;
    uint64_t idle_uid;
    Search search;
    Checkpoint search_checkpoint;
    HTerm *query;
    size_t query_count;
    Frame *work;
    size_t work_count, work_capacity, work_head;
    Hypothesis *hyps;
    size_t hyp_count, hyp_capacity;
    HypIndex *hyp_index;
    size_t hyp_index_count, hyp_index_capacity;
    Choice *choices;
    size_t choice_count, choice_capacity;
    uint64_t next_choice, step_floor, step_id;
    Assignment *assignments;
    size_t assignment_count, assignment_capacity;
    /* No assignment is ASSIGNMENT_OPEN (assignment_settled), and every one
        * that is made is there at a checkpoint that is not older than these. */
    size_t assignment_trail, assignment_heap;
    int assignment_settled;
    int assignment_dirty, settle_action;
    Frame current;
    size_t batch, permanent, collect_at, arena_collect_at, arena_spent, collect_step, collections;
    uint64_t host_state, next_call, origin;
    uint64_t view_token, last_view_token;
    size_t view_trail;
    int service_deltas, transient_output, scoped_exports;
    /* The predicates whose hypotheses a debugger host reads (focused). */
    size_t *focus, focus_count;
    int focused;
    HostRoots *host_roots;
    size_t host_roots_count, host_roots_used, host_roots_capacity;
    uint64_t *retired_tokens;
    size_t retired_count, retired_capacity;
    int action, debugging, assignment_failed, exhausted, answer_ready, resume_answer, end_debugged;
    int event_kind, event_continuation;
    int64_t event_aux;
    HTerm event_term, truth;
    int64_t *buffer;
    size_t buffer_count, buffer_capacity;
    const char *api_error;
    char api_message[192];
    char error[192];
};

static BucketIndex *uid_insert(HolV2Machine *m, BucketIndex *root, uint64_t uid, int *changed);
static BucketIndex *uid_remove(HolV2Machine *m, BucketIndex *root, uint64_t uid, int *changed);
static int uid_equal(BucketIndex *left, BucketIndex *right);
static BucketIndex *copy_tree(HolV2Machine *m, BucketIndex *source, int counted);

static HolV2Machine *clone_in(const HolV2Machine *source, HMemory *memory);
static void release_fields(HolV2Machine *m);

static int api_failure(HolV2Machine *m, int code, const char *message)
{
    size_t length = strlen(message);
    if (length >= sizeof(m->api_message)) length = sizeof(m->api_message) - 1;
    memmove(m->api_message, message, length);
    m->api_message[length] = '\0';
    m->api_error = m->api_message;
    m->api_code = code;
    atomic_store_explicit(&m->memory->fault, 0, memory_order_relaxed);
    return -1;
}

static int fail(HolV2Machine *m, const char *message)
{
    if (!m->error[0]) {
        int fault = atomic_load_explicit(&m->memory->fault, memory_order_relaxed);
        if (fault == 1) { message = "Native memory limit exceeded"; m->error_code = HV2_ERROR_MEMORY; }
        else if (fault == 2) m->error_code = HV2_ERROR_ALLOCATION;
        else if (m->terms && ht_error_code(m->terms) == HT_ERROR_WORK) m->error_code = HV2_ERROR_WORK;
        else if (!m->error_code) m->error_code = HV2_ERROR_INTERNAL;
        size_t n = strlen(message);
        if (n >= sizeof(m->error)) n = sizeof(m->error) - 1;
        memcpy(m->error, message, n);
        m->error[n] = '\0';
    }
    return 0;
}

static int push_word(HolV2Machine *m, int64_t word);
static int push_term(HolV2Machine *m, HTerm term);

/* Capture the offending term while its branch is live. Resource failure
    * during export remains a resource failure, never a logical rejection. */
static int invalid_term(HolV2Machine *m, int code, HTerm term, const char *message)
{
    if (m->error[0]) return 0;
    m->buffer_count = 0;
    m->transient_output = 1;
    int captured = push_word(m, 1) && push_term(m, term);
    m->transient_output = 0;
    if (!captured) return 0;
    m->error_code = code;
    return fail(m, message);
}

#define ROLE(m,index) (*(const int64_t *) hv_get(&(m)->program[TABLE_ROLES], (index)))
#define FACT(m,index) (*(const Fact *) hv_get(&(m)->program[TABLE_FACTS], (index)))
#define PREDICATE(m,index) (*(const Predicate *) hv_get(&(m)->program[TABLE_PREDICATES], (index)))
#define BUCKET(m,index) (*(const Bucket *) hv_get(&(m)->program[TABLE_BUCKETS], (index)))

static int copy_role(HMemory *memory, void *target, const void *source)
{
    hm_count(memory, HM_PROGRAM_ROWS, 1);
    memcpy(target, source, sizeof(int64_t));
    return 1;
}

static int copy_fact(HMemory *memory, void *target, const void *source)
{
    hm_count(memory, HM_PROGRAM_ROWS, 1);
    memcpy(target, source, sizeof(Fact));
    return 1;
}

static int copy_predicate(HMemory *memory, void *target, const void *source)
{
    hm_count(memory, HM_PROGRAM_ROWS, 1);
    memcpy(target, source, sizeof(Predicate));
    return 1;
}

static int copy_bucket(HMemory *memory, void *target, const void *source)
{
    hm_count(memory, HM_PROGRAM_ROWS, 1);
    memcpy(target, source, sizeof(Bucket));
    return 1;
}

static void *program_write(HolV2Machine *m, size_t kind, size_t index)
{
    void *value = hv_mutable(&m->program[kind], index);
    if (!value) fail(m, "V2 program path allocation failed");
    return value;
}

static int program_append(HolV2Machine *m, size_t kind, const void *value)
{
    return hv_append(&m->program[kind], value) || fail(m, "V2 program append allocation failed");
}

static int advance_version(HolV2Machine *m)
{
    ProgramVersion *version = hm_alloc(m->memory, sizeof(*version));
    if (!version) return fail(m, "V2 program version allocation failed");
    size_t own = sizeof(HMemoryHeader) + sizeof(*version);
    if (m->version && m->version->bytes > SIZE_MAX - own) { hm_free(version); return fail(m, "V2 program history size overflow"); }
    atomic_init(&version->references, 1);
    version->parent = m->version;
    version->bytes = own + (m->version ? m->version->bytes : 0);
    /* The old machine reference is transferred to the parent edge. */
    m->version = version;
    return 1;
}

static int term_ok(HolV2Machine *m, HTerm term)
{
    if (term != HT_NONE) return 1;
    int code = ht_error_code(m->terms);
    if (code == HT_ERROR_WORK) m->error_code = HV2_ERROR_WORK;
    if (code == HT_ERROR_MEMORY) m->error_code = HV2_ERROR_MEMORY;
    if (code == HT_ERROR_ALLOCATION) m->error_code = HV2_ERROR_ALLOCATION;
    return fail(m, ht_error(m->terms));
}

static void *grow(HolV2Machine *m, void *data, size_t *capacity, size_t count, size_t width);

/* grow retains the old pointer and capacity on failure. Assign through the
    * caller's typed lvalue: writing a T* through void** is not C11 alias-safe.
    * Arguments are stable lvalues/values without side effects. */
#define reserve(owner,pointer,capacity,count,width) \
    ((count) <= *(capacity) || \
        ((pointer) = grow((owner), (pointer), (capacity), (count), (width)), (count) <= *(capacity)))

static void *grow(HolV2Machine *m, void *data, size_t *capacity, size_t count, size_t width)
{
    if (count > SIZE_MAX / width) { fail(m, "V2 arena size overflow"); return data; }
    size_t next = *capacity ? *capacity : 32;
    while (next < count) {
        if (next > SIZE_MAX / 2) { next = count; break; }
        next *= 2;
    }
    if (next > SIZE_MAX / width) next = count;
    void *grown = hm_realloc(m->memory, data, next * width);
    if (!grown) { fail(m, "V2 arena allocation failed"); return data; }
    *capacity = next;
    return grown;
}

#define RESERVE(m,field,count) reserve((m), (m)->field, &(m)->field##_capacity, (count), sizeof(*(m)->field))

/* Constants, nominal UIDs and the unknown-head key occupy distinct domains.
    * No moving term handle participates in a key. Two tag bits plus the full
    * identity give a fixed 66-bit bound on every lookup/update path. */
static HypKey hypothesis_key(const HolV2Machine *m, HTerm head)
{
    if (head == HT_NONE) return (HypKey) { 0, 2 };
    HTView view = ht_view(m->terms, head);
    if (view.tag == HT_CONST) return (HypKey) { (uint64_t) view.symbol, 0 };
    if (view.tag == HT_NOMINAL) return (HypKey) { view.uid, 1 };
    return (HypKey) { 0, 2 };
}

static unsigned hypothesis_direction(HypKey key, size_t bit)
{
    return bit < 2 ? (key.kind >> (1 - bit)) & 1 : (unsigned) ((key.identity >> (65 - bit)) & 1);
}

static int hypothesis_key_equal(HypKey left, HypKey right)
{
    return left.kind == right.kind && left.identity == right.identity;
}

static size_t hypothesis_lookup(HolV2Machine *m, size_t root, HypKey key)
{
    if (root == NONE) return NONE;
    while (m->hyp_index[root].bit != NONE) {
        hm_count(m->memory, HM_VISITS, 1);
        HypIndex node = m->hyp_index[root];
        root = node.value.children[hypothesis_direction(key, node.bit)];
    }
    hm_count(m->memory, HM_VISITS, 1);
    HypIndex leaf = m->hyp_index[root];
    return hypothesis_key_equal(key, leaf.value.leaf.key) ? leaf.value.leaf.value : NONE;
}

static size_t hypothesis_node(HolV2Machine *m, HypIndex node, int growing)
{
    if (m->hyp_index_count == SIZE_MAX) { fail(m, "V2 hypothesis index overflow"); return NONE; }
    if (!growing && m->hyp_index_count >= m->hyp_index_capacity) {
        fail(m, "V2 hypothesis collection index exceeded its old capacity"); return NONE;
    }
    if (growing && !reserve(m, m->hyp_index, &m->hyp_index_capacity, m->hyp_index_count + 1, sizeof(*m->hyp_index))) return NONE;
    size_t at = m->hyp_index_count++;
    m->hyp_index[at] = node;
    hm_count(m->memory, HM_VISITS, 1);
    return at;
}

static size_t hypothesis_insert(HolV2Machine *m, size_t root, HypKey key, size_t value, int growing)
{
    HypIndex leaf = {0};
    leaf.bit = NONE;
    leaf.value.leaf.key = key;
    leaf.value.leaf.value = value;
    if (root == NONE) return hypothesis_node(m, leaf, growing);
    size_t old = root;
    while (m->hyp_index[old].bit != NONE) {
        hm_count(m->memory, HM_VISITS, 1);
        HypIndex node = m->hyp_index[old];
        old = node.value.children[hypothesis_direction(key, node.bit)];
    }
    HypKey previous = m->hyp_index[old].value.leaf.key;
    size_t differing = 0;
    if (hypothesis_key_equal(key, previous)) differing = NONE;
    else while (hypothesis_direction(key, differing) == hypothesis_direction(previous, differing)) ++differing;
    size_t path[66], count = 0;
    old = root;
    while (m->hyp_index[old].bit != NONE && m->hyp_index[old].bit < differing) {
        hm_count(m->memory, HM_VISITS, 1);
        path[count++] = old;
        HypIndex node = m->hyp_index[old];
        old = node.value.children[hypothesis_direction(key, node.bit)];
    }
    size_t result = hypothesis_node(m, leaf, growing);
    if (result == NONE) return NONE;
    if (differing != NONE) {
        unsigned direction = hypothesis_direction(key, differing);
        HypIndex parent = {0};
        parent.bit = differing;
        parent.value.children[direction] = result;
        parent.value.children[1 - direction] = old;
        result = hypothesis_node(m, parent, growing);
    }
    while (result != NONE && count) {
        HypIndex parent = m->hyp_index[path[--count]];
        parent.value.children[hypothesis_direction(key, parent.bit)] = result;
        result = hypothesis_node(m, parent, growing);
    }
    return result;
}

static int index_hypothesis(HolV2Machine *m, size_t at, int growing)
{
    Hypothesis *hyp = &m->hyps[at];
    size_t root = hyp->next == NONE ? NONE : m->hyps[hyp->next].index_root;
    HypKey key = hypothesis_key(m, hyp->rigid_head);
    hyp->same = hypothesis_lookup(m, root, key);
    size_t before = m->hyp_index_count;
    root = hypothesis_insert(m, root, key, at, growing);
    if (root == NONE) { m->hyp_index_count = before; return 0; }
    hyp->index_root = root;
    hyp->index_end = m->hyp_index_count;
    return 1;
}

static size_t next_hypothesis(const Search *search)
{
    if (!search->local_indexed || search->local_unknown == NONE) return search->local;
    return search->local == NONE || search->local_unknown > search->local ? search->local_unknown : search->local;
}

static void advance_hypothesis(const HolV2Machine *m, Search *search, size_t at)
{
    if (!search->local_indexed) search->local = m->hyps[at].next;
    else if (at == search->local) search->local = m->hyps[at].same;
    else search->local_unknown = m->hyps[at].same;
}

static Checkpoint checkpoint(const HolV2Machine *m)
{
    return (Checkpoint) { ht_checkpoint(m->terms), m->work_count, m->hyp_count, m->host_state, m->view_token, m->view_trail };
}

static size_t root_slot(const HostRoots *roots, size_t capacity, int kind, uint64_t token)
{
    uint64_t hash = (token ^ ((uint64_t) kind << 61)) * UINT64_C(0x9e3779b97f4a7c15);
    hash ^= hash >> 29;
    size_t at = (size_t) hash & (capacity - 1);
    while (roots[at].token && (roots[at].token != token || roots[at].kind != kind)) at = (at + 1) & (capacity - 1);
    return at;
}

static void clear_host_roots(HolV2Machine *m)
{
    for (size_t i = 0; i < m->host_roots_capacity; ++i) index_release(m->host_roots[i].set);
    hm_free(m->host_roots);
    m->host_roots = NULL;
    m->host_roots_count = m->host_roots_used = m->host_roots_capacity = 0;
}

static HostRoots *insert_root(HolV2Machine *m, int kind, uint64_t token)
{
    size_t at = m->host_roots_capacity ? root_slot(m->host_roots, m->host_roots_capacity, kind, token) : 0;
    if (m->host_roots_capacity && m->host_roots[at].token) return &m->host_roots[at];
    if (!m->host_roots_capacity || m->host_roots_used + 1 > m->host_roots_capacity / 2) {
        size_t capacity = 16;
        while (capacity / 2 < m->host_roots_count + 1) {
            if (capacity > SIZE_MAX / 2) { fail(m, "Host root table overflow"); return NULL; }
            capacity *= 2;
        }
        HostRoots *roots = hm_calloc(m->memory, capacity, sizeof(*roots));
        if (!roots) { fail(m, "Host root table allocation failed"); return NULL; }
        for (size_t i = 0; i < m->host_roots_capacity; ++i) {
            HostRoots old = m->host_roots[i];
            if (old.token && old.token != UINT64_MAX) roots[root_slot(roots, capacity, old.kind, old.token)] = old;
        }
        hm_free(m->host_roots);
        m->host_roots = roots;
        m->host_roots_capacity = capacity;
        m->host_roots_used = m->host_roots_count;
        at = root_slot(roots, capacity, kind, token);
    }
    HostRoots *entry = &m->host_roots[at];
    *entry = (HostRoots) { token, NULL, 0, kind, 0 };
    ++m->host_roots_used;
    ++m->host_roots_count;
    return entry;
}

static void erase_root(HolV2Machine *m, HostRoots *root)
{
    index_release(root->set);
    *root = (HostRoots) { UINT64_MAX, NULL, 0, 0, 0 };
    --m->host_roots_count;
}

/* kind2 counts view tokens; kind3 counts constraint-state tokens. These roots
    * have no UID payload. Counts cover the current state and saved choices. */
static int retain_token(HolV2Machine *m, int kind, uint64_t token)
{
    if (!m->service_deltas || !token) return 1;
    HostRoots *root = insert_root(m, kind, token);
    if (!root) return 0;
    if (root->count == SIZE_MAX) return fail(m, "Host token reference overflow");
    ++root->count;
    return 1;
}

static int release_token(HolV2Machine *m, int kind, uint64_t token)
{
    if (!m->service_deltas || !token || !m->host_roots_capacity) return 1;
    HostRoots *root = &m->host_roots[root_slot(m->host_roots, m->host_roots_capacity, kind, token)];
    if (!root->token) return 1;
    if (!root->count) return fail(m, "Host token reference underflow");
    if (--root->count) return 1;
    if (m->retired_count > SIZE_MAX - 2 || !reserve(m, m->retired_tokens, &m->retired_capacity, m->retired_count + 2, sizeof(*m->retired_tokens))) return 0;
    m->retired_tokens[m->retired_count++] = (uint64_t) (kind == 3 ? 0 : 1);
    m->retired_tokens[m->retired_count++] = token;
    erase_root(m, root);
    if (kind == 3 || kind == 2) {
        root = &m->host_roots[root_slot(m->host_roots, m->host_roots_capacity, kind == 3 ? 0 : 4, token)];
        if (root->token) erase_root(m, root);
    }
    return 1;
}

static int change_token(HolV2Machine *m, int kind, uint64_t *slot, uint64_t value)
{
    if (*slot == value) return 1;
    if (!retain_token(m, kind, value) || !release_token(m, kind, *slot)) return 0;
    *slot = value;
    return 1;
}

static int activate_service_deltas(HolV2Machine *m)
{
    if (m->service_deltas) return 1;
    m->service_deltas = 1;
    if (!retain_token(m, 3, m->host_state) || !retain_token(m, 2, m->view_token)) return 0;
    for (size_t i = 0; i < m->choice_count; ++i) {
        if (!retain_token(m, 3, m->choices[i].checkpoint.host) || !retain_token(m, 2, m->choices[i].checkpoint.view)) return 0;
    }
    return 1;
}

int hol_v2_register_host_roots(HolV2Machine *m, int kind, uint64_t token, const uint64_t *uids, size_t count)
{
    if (!m || m->error[0]) return -1;
    if ((kind != 0 && kind != 1) || !token || token > INT64_MAX || (count && !uids) || count > SIZE_MAX / sizeof(*uids)) return api_failure(m, HV2_ERROR_USAGE, "Invalid host root registration");
    for (size_t i = 0; i < count; ++i) {
        if (ht_lookup_uid(m->terms, uids[i]) == HT_NONE) return api_failure(m, HV2_ERROR_USAGE, "Host root registration names an expired identity");
    }
    BucketIndex *set = NULL;
    size_t members = 0;
    for (size_t i = 0; i < count; ++i) {
        int changed = 0;
        BucketIndex *next = uid_insert(m, set, uids[i], &changed);
        index_release(set);
        set = next;
        if (m->error[0]) { index_release(set); return -1; }
        members += (size_t) changed;
        ht_watch(m->terms, ht_lookup_uid(m->terms, uids[i]));
    }
    size_t at = m->host_roots_capacity ? root_slot(m->host_roots, m->host_roots_capacity, kind, token) : 0;
    if (m->host_roots_capacity && m->host_roots[at].token) {
        HostRoots *old = &m->host_roots[at];
        int same = old->count == members && uid_equal(old->set, set);
        index_release(set);
        return same ? 1 : api_failure(m, HV2_ERROR_USAGE, "A host root token is immutable");
    }
    HostRoots *entry = insert_root(m, kind, token);
    if (!entry) { index_release(set); return -1; }
    *entry = (HostRoots) { token, set, members, kind, 0 };
    return 1;
}

static int apply_assignments(HolV2Machine *m, size_t trail, size_t heap);

static int restore_checkpoint(HolV2Machine *m, Checkpoint saved)
{
    if (!ht_restore(m->terms, saved.terms)) return fail(m, ht_error(m->terms));
    m->work_count = saved.work;
    m->hyp_count = saved.hyps;
    m->hyp_index_count = saved.hyps ? m->hyps[saved.hyps - 1].index_end : 0;
    if (!change_token(m, 3, &m->host_state, saved.host) || !change_token(m, 2, &m->view_token, saved.view)) return 0;
    m->view_trail = saved.view_trail;
    return apply_assignments(m, saved.terms.trail, saved.terms.heap);
}

static size_t push_frame(HolV2Machine *m, Frame frame)
{
    if (m->work_count == SIZE_MAX || !RESERVE(m, work, m->work_count + 1)) return NONE;
    size_t result = m->work_count++;
    if (m->arena_spent != SIZE_MAX) ++m->arena_spent;
    m->work[result] = frame;
    return result;
}

static int schedule(HolV2Machine *m, HTerm goal, Frame environment, size_t next)
{
    environment.goal = goal;
    environment.next = next;
    size_t result = push_frame(m, environment);
    if (result == NONE) return 0;
    m->work_head = result;
    m->end_debugged = 0;
    m->action = ACTION_NEXT;
    return 1;
}

static int push_choice(HolV2Machine *m, Choice choice)
{
    if (m->next_choice == UINT64_MAX) return fail(m, "V2 choice identity exhausted");
    if (m->choice_count == SIZE_MAX || !reserve(m, m->choices, &m->choice_capacity, m->choice_count + 1, sizeof(*m->choices))) return 0;
    choice.serial = m->next_choice++;
    m->choices[m->choice_count++] = choice;
    return retain_token(m, 3, choice.checkpoint.host) && retain_token(m, 2, choice.checkpoint.view);
}

static int role(const HolV2Machine *m, HTerm head)
{
    HTView view = ht_view(m->terms, ht_deref(m->terms, head));
    return view.tag == HT_CONST && view.symbol < m->symbol_count ? (int) ROLE(m, view.symbol) : HV2_ORDINARY;
}

/* A role that only describes a constant. */
static int ordinary(int operation)
{
    return operation == HV2_ORDINARY || operation == HV2_ARITHMETIC || operation == HV2_NATURAL || operation == HV2_ARROW || operation == HV2_TYPE;
}

static int same_head(const HolV2Machine *m, HTerm left, HTerm right)
{
    HTView lhs = ht_view(m->terms, ht_deref(m->terms, left));
    HTView rhs = ht_view(m->terms, ht_deref(m->terms, right));
    if (lhs.tag != rhs.tag) return 0;
    if (lhs.tag == HT_CONST) return lhs.symbol == rhs.symbol;
    if (lhs.tag == HT_NOMINAL) return lhs.uid == rhs.uid;
    return 0;
}

static int event(HolV2Machine *m, int kind, HTerm term, int continuation, int64_t auxiliary)
{
    if (kind == HV2_EVENT_SETTLE) m->assignment_dirty = 0;
    m->event_kind = kind;
    m->event_term = term;
    m->event_continuation = continuation;
    m->event_aux = auxiliary;
    return 1;
}

static HTerm true_term(HolV2Machine *m)
{
    if (m->truth != HT_NONE) return m->truth;
    for (size_t i = 0; i < m->symbol_count; ++i) {
        if (ROLE(m, i) == HV2_TRUE) return ht_constant(m->terms, i, -1);
    }
    fail(m, "V2 symbol table has no true operator");
    return HT_NONE;
}

static int normalized_spine(HolV2Machine *m, HTerm term, HTSpine *spine)
{
    HTerm normalized = ht_normalize(m->terms, term, HT_HNF);
    return normalized != HT_NONE && ht_spine(m->terms, normalized, spine);
}

/* 1: the head of term, below its leading abstractions, is an unbound variable;
    * 0: it is anything else; -1: store error. Nothing is bound. */
static int flexible_head(HolV2Machine *m, HTerm term)
{
    HTerm body = ht_normalize(m->terms, term, HT_HNF);
    if (body == HT_NONE) return -1;
    for (;;) {
        HTView view = ht_view(m->terms, ht_deref(m->terms, body));
        if (view.tag != HT_LAM) break;
        body = view.a;
    }
    HTSpine spine;
    if (!ht_spine(m->terms, body, &spine)) return -1;
    int tag = ht_view(m->terms, ht_deref(m->terms, spine.head)).tag;
    ht_spine_free(&spine);
    return tag == HT_VAR || tag == HT_WILD;
}

#define PREFIX_LIMIT 32

/* The literal shape of a clause: pi (x\ pi (y\ ... head :- body)). Its
    * binders are instantiated together, and its body only after the head has
    * matched. Any other shape takes the general path of instantiate_fact. */
typedef struct {
    int is_type[PREFIX_LIMIT];
    int64_t meta[PREFIX_LIMIT];
    HTerm types[PREFIX_LIMIT];
    HTerm values[PREFIX_LIMIT];
    size_t count;
    HTerm head, body;
} Clause;

static HTerm rigid_head_of(const HolV2Machine *m, HTerm term, size_t *arity)
{
    size_t budget = 4096;
    *arity = 0;
    for (;;) {
        term = ht_deref(m->terms, term);
        HTView view = ht_view(m->terms, term);
        if (view.tag != HT_APP) return view.tag == HT_CONST || view.tag == HT_NOMINAL ? term : HT_NONE;
        if (!budget--) return HT_NONE;
        ++*arity;
        term = view.a;
    }
}

static void clause_shape(const HolV2Machine *m, HTerm fact, Clause *clause)
{
    HTerm term = ht_deref(m->terms, fact);
    clause->count = 0;
    while (clause->count < PREFIX_LIMIT) {
        HTView application = ht_view(m->terms, term);
        if (application.tag != HT_APP || ht_view(m->terms, ht_deref(m->terms, application.a)).tag != HT_CONST) break;
        int operation = role(m, application.a);
        HTView function = ht_view(m->terms, ht_deref(m->terms, application.b));
        if ((operation != HV2_PI && operation != HV2_TY_PI) || function.tag != HT_LAM) break;
        clause->is_type[clause->count] = operation == HV2_TY_PI;
        clause->meta[clause->count] = function.meta;
        clause->types[clause->count] = function.b;
        ++clause->count;
        term = ht_deref(m->terms, function.a);
    }
    clause->head = HT_NONE;
    clause->body = HT_NONE;
    HTView outer = ht_view(m->terms, term);
    HTView inner = ht_view(m->terms, outer.tag == HT_APP ? ht_deref(m->terms, outer.a) : HT_NONE);
    size_t arity;
    if (inner.tag == HT_APP && ht_view(m->terms, ht_deref(m->terms, inner.a)).tag == HT_CONST && role(m, inner.a) == HV2_IF) {
        clause->head = inner.b;
        clause->body = outer.b;
    } else {
        HTerm head = rigid_head_of(m, term, &arity);
        if (head != HT_NONE && (ht_view(m->terms, head).tag == HT_NOMINAL || ordinary(role(m, head)))) clause->head = term;
    }
}

/* Two arguments whose rigid heads differ cannot unify, and neither can two
    * different naturals. A natural against a successor term, and an opaque
    * formula, are compared by the unifier alone. */
static int rigid_clash(const HolV2Machine *m, HTerm goal, HTerm pattern)
{
    size_t arity;
    HTView number = ht_view(m->terms, ht_deref(m->terms, goal)), other = ht_view(m->terms, ht_deref(m->terms, pattern));
    if (number.tag == HT_NAT && other.tag == HT_NAT) return strcmp(number.digits, other.digits) != 0;
    HTerm left = rigid_head_of(m, goal, &arity), right = rigid_head_of(m, pattern, &arity);
    if (left == HT_NONE || right == HT_NONE) return 0;
    HTView lhs = ht_view(m->terms, left), rhs = ht_view(m->terms, right);
    if ((lhs.tag == HT_CONST && !ordinary(role(m, left))) || (rhs.tag == HT_CONST && !ordinary(role(m, right)))) return 0;
    if (lhs.tag != rhs.tag) return 1;
    return lhs.tag == HT_CONST ? lhs.symbol != rhs.symbol : lhs.uid != rhs.uid;
}

/* Whether a literal clause head, with the rigid head and the arity it has, is
    * certain not to match the goal of a plain search. */
static int shape_clash(const HolV2Machine *m, const Search *search, HTerm clause_head, HTerm head, size_t arity, uint64_t mask)
{
    if (!same_head(m, search->head, head)) return 1;
    if (arity != search->arity) return 0;
    HTerm goal = ht_deref(m->terms, search->goal), pattern = ht_deref(m->terms, clause_head);
    while (arity-- && mask) {
        HTView left = ht_view(m->terms, goal), right = ht_view(m->terms, pattern);
        if (left.tag != HT_APP || right.tag != HT_APP) return 0;
        if ((mask & 1) && rigid_clash(m, left.b, right.b)) return 1;
        if (mask != UINT64_MAX) mask >>= 1;
        goal = ht_deref(m->terms, left.a);
        pattern = ht_deref(m->terms, right.a);
    }
    return 0;
}

/* Whether a clause head of this literal shape is certain not to match. */
static int head_clash(const HolV2Machine *m, const Search *search, HTerm fact)
{
    Clause clause;
    if (!search->plain) return 0;
    clause_shape(m, fact, &clause);
    if (clause.head == HT_NONE) return 0;
    size_t arity;
    HTerm head = rigid_head_of(m, clause.head, &arity);
    return head != HT_NONE && shape_clash(m, search, clause.head, head, arity, UINT64_MAX);
}

static int fact_clash(const HolV2Machine *m, const Search *search, const Fact *fact)
{
    if (fact->rigid == HT_NONE) return head_clash(m, search, fact->fact);
    return search->plain && shape_clash(m, search, fact->head, fact->rigid, fact->arity, fact->clash_args);
}

/* What an argument shows without being reduced: a natural literal, or the
    * rigid head of an application. rigid_clash decides by exactly these. */
static Key argument_key(const HolV2Machine *m, HTerm argument)
{
    HTerm term = ht_deref(m->terms, argument);
    if (ht_view(m->terms, term).tag == HT_NAT) return (Key) { KEY_NATURAL, 0, term };
    size_t arity;
    HTerm head = rigid_head_of(m, term, &arity);
    if (head == HT_NONE) return (Key) { KEY_NONE, 0, HT_NONE };
    HTView view = ht_view(m->terms, head);
    if (view.tag == HT_NOMINAL) return (Key) { KEY_NOMINAL, 0, HT_NONE };
    return ordinary(role(m, head)) ? (Key) { KEY_CONSTANT, view.symbol, HT_NONE } : (Key) { KEY_NONE, 0, HT_NONE };
}

/* The first argument of a literal application with arity >= 1 arguments. */
static HTerm first_argument(const HolV2Machine *m, HTerm term, size_t arity)
{
    term = ht_deref(m->terms, term);
    while (arity-- > 1) term = ht_deref(m->terms, ht_view(m->terms, term).a);
    return ht_view(m->terms, term).b;
}

/* The literal application `term` of arity >= 1 arguments with another first
    * argument. */
static HTerm with_first_argument(HolV2Machine *m, HTerm term, size_t arity, HTerm argument)
{
    HTView view = ht_view(m->terms, ht_deref(m->terms, term));
    if (arity == 1) return ht_app(m->terms, view.a, argument, view.meta);
    HTerm function = with_first_argument(m, view.a, arity - 1, argument);
    return function == HT_NONE ? HT_NONE : ht_app(m->terms, function, view.b, view.meta);
}

typedef struct {
    uint64_t symbol, constant;
    const char *digits;
    size_t length;
} IndexKey;

static IndexKey index_key(const HolV2Machine *m, size_t symbol, Key key)
{
    const char *digits = key.kind == KEY_NATURAL ? ht_view(m->terms, key.literal).digits : NULL;
    return (IndexKey) { (uint64_t) symbol, (uint64_t) key.symbol, digits, digits ? strlen(digits) : 0 };
}

static IndexKey bucket_key(const HolV2Machine *m, const Bucket *bucket)
{
    Key key = { bucket->literal == HT_NONE ? KEY_CONSTANT : KEY_NATURAL, bucket->key, bucket->literal };
    return index_key(m, bucket->symbol, key);
}

/* Fixed-width predicate, a natural/constant tag, then the exact key. Natural
    * digits have a zero terminator; no decimal digit is zero, so prefixes and
    * adversarial hash collisions remain distinct without collision chains. */
static unsigned index_byte(IndexKey key, size_t byte)
{
    if (byte < 8) return (unsigned) ((key.symbol >> (8 * (7 - byte))) & 255);
    if (byte == 8) return key.digits != NULL;
    byte -= 9;
    if (key.digits) return byte < key.length ? (unsigned char) key.digits[byte] : 0;
    return byte < 8 ? (unsigned) ((key.constant >> (8 * (7 - byte))) & 255) : 0;
}

static unsigned index_direction(IndexKey key, size_t bit)
{
    return (index_byte(key, bit / 8) >> (7 - bit % 8)) & 1;
}

static size_t index_difference(IndexKey a, IndexKey b)
{
    size_t length = a.length > b.length ? a.length : b.length;
    if (length < 8) length = 8;
    if (length > SIZE_MAX / 8 - 10) return NONE;
    for (size_t byte = 0; byte < 10 + length; ++byte) {
        unsigned different = index_byte(a, byte) ^ index_byte(b, byte);
        if (!different) continue;
        size_t bit = 0;
        while (!(different & 128)) { different <<= 1; ++bit; }
        return byte * 8 + bit;
    }
    return NONE;
}

static BucketIndex *tree_node(HolV2Machine *m, size_t bit, size_t bucket, BucketIndex *left, BucketIndex *right, int counted)
{
    BucketIndex *node = hm_calloc(m->memory, 1, sizeof(*node));
    if (!node) { fail(m, "V2 fact-index node allocation failed"); return NULL; }
    atomic_init(&node->references, 1);
    node->bit = bit;
    node->bytes = sizeof(HMemoryHeader) + sizeof(*node);
    if (bit == NONE) node->value.bucket = bucket;
    else {
        if (left->bytes > SIZE_MAX - node->bytes || right->bytes > SIZE_MAX - node->bytes - left->bytes) {
            hm_free(node); fail(m, "V2 fact-index byte count overflow"); return NULL;
        }
        node->value.children[0] = left;
        node->value.children[1] = right;
        index_retain(left);
        index_retain(right);
        node->bytes += left->bytes + right->bytes;
    }
    if (counted) hm_count(m->memory, HM_PROGRAM_ROWS, 1);
    return node;
}

static BucketIndex *index_node(HolV2Machine *m, size_t bit, size_t bucket, BucketIndex *left, BucketIndex *right)
{
    return tree_node(m, bit, bucket, left, right, 1);
}

static unsigned uid_direction(uint64_t uid, size_t bit)
{
    return (unsigned) ((uid >> (63 - bit)) & 1);
}

static BucketIndex *uid_insert(HolV2Machine *m, BucketIndex *root, uint64_t uid, int *changed)
{
    *changed = 0;
    if (uid > SIZE_MAX) { fail(m, "Host root UID exceeds the native address range"); return NULL; }
    if (!root) {
        BucketIndex *leaf = tree_node(m, NONE, (size_t) uid, NULL, NULL, 0);
        *changed = leaf != NULL;
        return leaf;
    }
    BucketIndex *leaf = root;
    while (leaf->bit != NONE) leaf = leaf->value.children[uid_direction(uid, leaf->bit)];
    uint64_t difference = uid ^ (uint64_t) leaf->value.bucket;
    if (!difference) { index_retain(root); return root; }
    size_t bit = 0;
    while (!(difference & (UINT64_C(1) << 63))) { difference <<= 1; ++bit; }
    BucketIndex *path[64], *old = root;
    size_t count = 0;
    while (old->bit != NONE && old->bit < bit) {
        path[count++] = old;
        old = old->value.children[uid_direction(uid, old->bit)];
    }
    leaf = tree_node(m, NONE, (size_t) uid, NULL, NULL, 0);
    if (!leaf) return NULL;
    unsigned direction = uid_direction(uid, bit);
    BucketIndex *result = tree_node(m, bit, 0, direction ? old : leaf, direction ? leaf : old, 0);
    index_release(leaf);
    while (result && count) {
        BucketIndex *parent = path[--count];
        direction = uid_direction(uid, parent->bit);
        BucketIndex *next = tree_node(m, parent->bit, 0,
            direction ? parent->value.children[0] : result,
            direction ? result : parent->value.children[1], 0);
        index_release(result);
        result = next;
    }
    *changed = result != NULL;
    return result;
}

static BucketIndex *uid_remove(HolV2Machine *m, BucketIndex *root, uint64_t uid, int *changed)
{
    *changed = 0;
    if (!root) return NULL;
    BucketIndex *path[64], *leaf = root;
    size_t count = 0;
    while (leaf->bit != NONE) {
        path[count++] = leaf;
        leaf = leaf->value.children[uid_direction(uid, leaf->bit)];
    }
    if ((uint64_t) leaf->value.bucket != uid) { index_retain(root); return root; }
    *changed = 1;
    if (!count) return NULL;
    BucketIndex *parent = path[--count];
    BucketIndex *result = parent->value.children[1 - uid_direction(uid, parent->bit)];
    index_retain(result);
    while (result && count) {
        parent = path[--count];
        unsigned direction = uid_direction(uid, parent->bit);
        BucketIndex *next = tree_node(m, parent->bit, 0,
            direction ? parent->value.children[0] : result,
            direction ? result : parent->value.children[1], 0);
        index_release(result);
        result = next;
    }
    return result;
}

static int uid_contains(BucketIndex *root, uint64_t uid)
{
    if (!root) return 0;
    while (root->bit != NONE) root = root->value.children[uid_direction(uid, root->bit)];
    return (uint64_t) root->value.bucket == uid;
}

static int uid_equal(BucketIndex *left, BucketIndex *right)
{
    struct { BucketIndex *left, *right; } stack[65];
    size_t count = 0;
    for (;;) {
        if (left != right) {
            if (!left || !right || left->bit != right->bit) return 0;
            if (left->bit == NONE) {
                if (left->value.bucket != right->value.bucket) return 0;
            } else {
                stack[count].left = left->value.children[1];
                stack[count++].right = right->value.children[1];
                left = left->value.children[0];
                right = right->value.children[0];
                continue;
            }
        }
        if (!count) return 1;
        left = stack[--count].left;
        right = stack[count].right;
    }
}

static size_t find_bucket_index(const HolV2Machine *m, size_t symbol, Key key)
{
    BucketIndex *node = m->bucket_index;
    if (!node) return NONE;
    IndexKey wanted = index_key(m, symbol, key);
    while (node->bit != NONE) node = node->value.children[index_direction(wanted, node->bit)];
    return index_difference(wanted, bucket_key(m, &BUCKET(m, node->value.bucket))) == NONE ? node->value.bucket : NONE;
}

static const Bucket *find_bucket(const HolV2Machine *m, size_t symbol, Key key)
{
    size_t index = find_bucket_index(m, symbol, key);
    return index == NONE ? NULL : &BUCKET(m, index);
}

/* Functional path copy. Publishing the new root is the final action, so any
    * allocation failure leaves the previous index intact. Buckets themselves
    * have stable vector positions across snapshots and program extensions. */
static int insert_bucket(HolV2Machine *m, size_t bucket)
{
    IndexKey key = bucket_key(m, &BUCKET(m, bucket));
    BucketIndex *old = m->bucket_index;
    if (!old) {
        m->bucket_index = index_node(m, NONE, bucket, NULL, NULL);
        return m->bucket_index != NULL;
    }
    BucketIndex *leaf = old;
    while (leaf->bit != NONE) leaf = leaf->value.children[index_direction(key, leaf->bit)];
    size_t bit = index_difference(key, bucket_key(m, &BUCKET(m, leaf->value.bucket)));
    if (bit == NONE) return fail(m, "Duplicate V2 fact-index key");
    BucketIndex **path = NULL;
    size_t count = 0, capacity = 0;
    while (old->bit != NONE && old->bit < bit) {
        if (!reserve(m, path, &capacity, count + 1, sizeof(*path))) { hm_free(path); return 0; }
        path[count++] = old;
        old = old->value.children[index_direction(key, old->bit)];
    }
    leaf = index_node(m, NONE, bucket, NULL, NULL);
    if (!leaf) { hm_free(path); return 0; }
    unsigned direction = index_direction(key, bit);
    BucketIndex *result = index_node(m, bit, 0, direction ? old : leaf, direction ? leaf : old);
    index_release(leaf);
    while (result && count) {
        BucketIndex *parent = path[--count];
        direction = index_direction(key, parent->bit);
        BucketIndex *next = index_node(m, parent->bit, 0,
            direction ? parent->value.children[0] : result,
            direction ? result : parent->value.children[1]);
        index_release(result);
        result = next;
    }
    hm_free(path);
    if (!result) return 0;
    index_release(m->bucket_index);
    m->bucket_index = result;
    return 1;
}

typedef struct { BucketIndex *source, *copy; } IndexCopy;

static BucketIndex *copy_tree_node(HolV2Machine *m, const BucketIndex *source, int counted)
{
    BucketIndex *copy = hm_calloc(m->memory, 1, sizeof(*copy));
    if (!copy) { fail(m, "V2 fact-index copy allocation failed"); return NULL; }
    atomic_init(&copy->references, 1);
    copy->bit = source->bit;
    copy->bytes = source->bytes;
    if (source->bit == NONE) copy->value.bucket = source->value.bucket;
    if (counted) hm_count(m->memory, HM_PROGRAM_ROWS, 1);
    return copy;
}

static BucketIndex *copy_tree(HolV2Machine *m, BucketIndex *source, int counted)
{
    if (!source) return NULL;
    BucketIndex *root = copy_tree_node(m, source, counted);
    if (!root) return NULL;
    IndexCopy *stack = NULL;
    size_t count = 0, capacity = 0;
    int success = reserve(m, stack, &capacity, 1, sizeof(*stack));
    if (success) stack[count++] = (IndexCopy) { source, root };
    while (success && count) {
        IndexCopy frame = stack[--count];
        if (frame.source->bit == NONE) continue;
        for (size_t i = 0; success && i < 2; ++i) {
            BucketIndex *child = copy_tree_node(m, frame.source->value.children[i], counted);
            if (!child) { success = 0; break; }
            frame.copy->value.children[i] = child;
            success = reserve(m, stack, &capacity, count + 1, sizeof(*stack));
            if (success) stack[count++] = (IndexCopy) { frame.source->value.children[i], child };
        }
    }
    hm_free(stack);
    if (!success) { index_release(root); return NULL; }
    return root;
}

/* Files the newest fact under its predicate, after the older ones. A fact
    * whose head is literally the predicate applied to arguments has the key of
    * its first argument when that is a natural or has an ordinary constant head.
    * A predicate whose keyed facts differ in arity, or have keys of both kinds,
    * is searched without the index. */
static int index_fact(HolV2Machine *m, size_t at)
{
    Fact *fact = program_write(m, TABLE_FACTS, at);
    if (!fact) return 0;
    Clause clause;
    size_t arity = 0;
    clause_shape(m, fact->fact, &clause);
    HTerm head = clause.head == HT_NONE ? HT_NONE : rigid_head_of(m, clause.head, &arity);
    fact->next = NONE;
    fact->peer = NONE;
    fact->rigid = head;
    if (head != HT_NONE) {
        fact->head = clause.head;
        fact->body = clause.body;
        fact->binders = clause.count;
        fact->arity = arity;
        for (size_t i = 0; i < clause.count; ++i) {
            if (clause.is_type[i]) fact->type_binders |= UINT32_C(1) << i;
        }
        HTerm argument_spine = clause.head;
        if (fact->arity > 64) fact->clash_args = UINT64_MAX;
        else for (size_t i = 0; i < fact->arity; ++i) {
            HTView application = ht_view(m->terms, ht_deref(m->terms, argument_spine));
            HTView pattern = ht_view(m->terms, ht_deref(m->terms, application.b));
            if (pattern.tag != HT_INDEX && pattern.tag != HT_WILD) fact->clash_args |= UINT64_C(1) << i;
            argument_spine = application.a;
        }
    }
    if (fact->symbol < 0) {
        if (m->dynamic_last == NONE) m->dynamic_first = at;
        else { Fact *previous = program_write(m, TABLE_FACTS, m->dynamic_last); if (!previous) return 0; previous->next = at; }
        m->dynamic_last = at;
        return 1;
    }
    Predicate *predicate = program_write(m, TABLE_PREDICATES, (size_t) fact->symbol);
    if (!predicate) return 0;
    if (predicate->last == NONE) predicate->first = at;
    else { Fact *previous = program_write(m, TABLE_FACTS, predicate->last); if (!previous) return 0; previous->next = at; }
    predicate->last = at;
    Key key = { KEY_NONE, 0, HT_NONE };
    if (head != HT_NONE && arity) {
        HTView view = ht_view(m->terms, head);
        if (view.tag == HT_CONST && view.symbol == (size_t) fact->symbol) key = argument_key(m, first_argument(m, clause.head, arity));
    }
    if (key.kind != KEY_NATURAL && key.kind != KEY_CONSTANT) {
        if (predicate->plain_last == NONE) predicate->plain_first = at;
        else { Fact *previous = program_write(m, TABLE_FACTS, predicate->plain_last); if (!previous) return 0; previous->peer = at; }
        predicate->plain_last = at;
        return 1;
    }
    if (predicate->arity == NONE) predicate->arity = arity;
    else if (predicate->arity != arity) predicate->mixed = 1;
    predicate->kinds |= key.kind == KEY_NATURAL ? 1 : 2;
    if (predicate->kinds == 3) predicate->mixed = 1;
    size_t bucket_at = find_bucket_index(m, (size_t) fact->symbol, key);
    if (bucket_at == NONE) {
        Bucket bucket = { (size_t) fact->symbol, key.symbol, key.literal, at, at };
        bucket_at = m->bucket_count;
        if (!program_append(m, TABLE_BUCKETS, &bucket) || !insert_bucket(m, bucket_at)) return 0;
        ++m->bucket_count;
    } else {
        Bucket *bucket = program_write(m, TABLE_BUCKETS, bucket_at);
        if (!bucket) return 0;
        Fact *previous = program_write(m, TABLE_FACTS, bucket->last);
        if (!previous) return 0;
        previous->peer = at;
        bucket->last = at;
    }
    return 1;
}

/* The candidates of a search come from up to four chains in source order. */
static size_t next_fact(const Search *search)
{
    size_t candidate = search->global < search->dynamic ? search->global : search->dynamic;
    if (search->keyed < candidate) candidate = search->keyed;
    return search->unkeyed < candidate ? search->unkeyed : candidate;
}

static void advance_fact(const HolV2Machine *m, Search *search, size_t candidate)
{
    if (candidate == search->global) search->global = FACT(m, candidate).next;
    else if (candidate == search->keyed) search->keyed = FACT(m, candidate).peer;
    else if (candidate == search->unkeyed) search->unkeyed = FACT(m, candidate).peer;
    else search->dynamic = FACT(m, candidate).next;
}

static int instantiate_head(HolV2Machine *m, HTerm fact, size_t scope, Clause *clause, HTerm *head)
{
    clause_shape(m, fact, clause);
    if (clause->head == HT_NONE) return 0;
    for (size_t i = 0; i < clause->count; ++i) {
        HTerm type = clause->types[i];
        if (type != HT_NONE && i) type = ht_instantiate(m->terms, type, clause->values, i);
        if (clause->types[i] != HT_NONE && !term_ok(m, type)) return -1;
        clause->values[i] = ht_var_typed(m->terms, scope, clause->is_type[i], clause->meta[i], type);
        if (!term_ok(m, clause->values[i])) return -1;
    }
    *head = clause->count ? ht_instantiate(m->terms, clause->head, clause->values, clause->count) : clause->head;
    return term_ok(m, *head) ? 1 : -1;
}

/* instantiate_head for a fact whose shape was read when it was loaded. */
static int instantiate_known(HolV2Machine *m, const Fact *fact, size_t scope, Clause *clause, HTerm *head)
{
    clause->count = fact->binders;
    clause->head = fact->head;
    clause->body = fact->body;
    if (!ht_open_binders(m->terms, fact->fact, scope, fact->type_binders, clause->values, fact->binders)) {
        fail(m, ht_error(m->terms));
        return -1;
    }
    *head = fact->head;
    return term_ok(m, *head) ? 1 : -1;
}

static int instantiate_fact(HolV2Machine *m, HTerm fact, size_t scope, HTerm *head, HTerm *body)
{
    for (;;) {
        HTSpine spine;
        if (!normalized_spine(m, fact, &spine)) return fail(m, ht_error(m->terms));
        int operation = role(m, spine.head);
        if ((operation == HV2_PI || operation == HV2_TY_PI) && spine.count == 1) {
            HTerm function = ht_normalize(m->terms, spine.args[0], HT_HNF);
            if (!term_ok(m, function)) { ht_spine_free(&spine); return 0; }
            HTView view = ht_view(m->terms, function);
            int64_t meta = view.tag == HT_LAM ? view.meta : -1;
            HTerm variable = ht_var_typed(m->terms, scope, operation == HV2_TY_PI, meta, view.tag == HT_LAM ? view.b : HT_NONE);
            ht_spine_free(&spine);
            if (!term_ok(m, variable)) return 0;
            fact = ht_apply(m->terms, function, variable);
            if (!term_ok(m, fact)) return 0;
        } else {
            if (operation == HV2_IF && spine.count == 2) {
                *head = spine.args[0];
                *body = spine.args[1];
            } else if (operation >= HV2_TY_PI && operation <= HV2_IS) {
                ht_spine_free(&spine);
                return invalid_term(m, HV2_ERROR_INVALID_FACT, fact, "Invalid V2 logical clause");
            } else {
                *head = fact;
                *body = true_term(m);
            }
            ht_spine_free(&spine);
            return term_ok(m, *body);
        }
    }
}

static int search_has_alternative(const Search *search)
{
    if (search->phase == SEARCH_GLOBAL || search->phase == SEARCH_EQUAL_GLOBAL) {
        return next_fact(search) != NONE || (search->phase == SEARCH_GLOBAL && next_hypothesis(search) != NONE);
    }
    return next_hypothesis(search) != NONE || (search->phase == SEARCH_EQUAL_LOCAL && search->fallback);
}

static void schedule_search(HolV2Machine *m, Search search, Checkpoint saved)
{
    m->search = search;
    m->search_checkpoint = saved;
    m->action = ACTION_SEARCH;
}

/* Advances past candidates that are certain not to match in the state of the
    * search checkpoint. Later bindings only add clashes, so a resumed
    * alternative skips them soundly. Every skipped candidate consumes the
    * scheduler batch like a failed trial; 0 reports an exhausted batch. */
static int skip_excluded(HolV2Machine *m, Search *search)
{
    if (!search->plain) return 1;
    if (search->phase == SEARCH_GLOBAL || search->phase == SEARCH_EQUAL_GLOBAL) {
        for (;;) {
            size_t candidate = next_fact(search);
            if (candidate == NONE) break;
            if (m->batch >= BATCH) return 0;
            if (!fact_clash(m, search, &FACT(m, candidate))) return 1;
            ++m->batch;
            advance_fact(m, search, candidate);
        }
        if (search->phase == SEARCH_EQUAL_GLOBAL) return 1;
    }
    while (next_hypothesis(search) != NONE) {
        size_t at = next_hypothesis(search);
        Hypothesis candidate = m->hyps[at];
        if (m->batch >= BATCH) return 0;
        int excluded = candidate.rigid_head != HT_NONE && !same_head(m, search->head, candidate.rigid_head);
        if (!excluded && !head_clash(m, search, candidate.fact)) return 1;
        ++m->batch;
        advance_hypothesis(m, search, at);
    }
    return 1;
}

/* One candidate or phase transition per scheduler step permits cancellation. */
static int search_step(HolV2Machine *m)
{
    Search *search = &m->search;
    Checkpoint saved = m->search_checkpoint;
    if (!restore_checkpoint(m, saved)) return 0;
    if (!skip_excluded(m, search)) return 1;
    HTerm fact;
    const Fact *known = NULL;
    if (search->phase == SEARCH_GLOBAL || search->phase == SEARCH_EQUAL_GLOBAL) {
        size_t candidate = next_fact(search);
        if (candidate == NONE) {
            if (search->phase == SEARCH_EQUAL_GLOBAL) return 0;
            search->phase = SEARCH_LOCAL;
            return 1;
        }
        fact = FACT(m, candidate).fact;
        if (FACT(m, candidate).rigid != HT_NONE) known = &FACT(m, candidate);
        advance_fact(m, search, candidate);
    } else {
        if (next_hypothesis(search) != NONE) {
            size_t at = next_hypothesis(search);
            Hypothesis candidate = m->hyps[at];
            advance_hypothesis(m, search, at);
            if (candidate.rigid_head != HT_NONE && !same_head(m, search->head, candidate.rigid_head)) return 1;
            fact = candidate.fact;
        } else if (search->phase == SEARCH_EQUAL_LOCAL && search->fallback) {
            if (search->equality == 2) {
                m->work_head = search->frame.next;
                m->action = ACTION_NEXT;
                return 1;
            }
            if (search->equality == 3) return 0;
            search->phase = SEARCH_EQUAL_GLOBAL;
            return 1;
        } else {
            return 0;
        }
    }
    skip_excluded(m, search);
    Clause clause;
    HTerm head = HT_NONE, body = HT_NONE;
    int literal, matches;
    size_t arity;
    if (known) {
        /* the head is the rigid application that the fact was loaded with */
        literal = instantiate_known(m, known, search->frame.scope, &clause, &head);
        if (literal < 0) return 0;
        matches = same_head(m, search->head, known->rigid);
        arity = known->arity;
    } else {
        literal = instantiate_head(m, fact, search->frame.scope, &clause, &head);
        if (literal < 0 || (!literal && !instantiate_fact(m, fact, search->frame.scope, &head, &body))) return 0;
        HTSpine spine;
        if (!normalized_spine(m, head, &spine)) return fail(m, ht_error(m->terms));
        matches = same_head(m, search->head, spine.head);
        arity = spine.count;
        ht_spine_free(&spine);
    }
    if (!matches) return 1;
    if (arity != search->arity) {
        if (known && clause.count) head = ht_instantiate(m->terms, head, clause.values, clause.count);
        return term_ok(m, head) && invalid_term(m, HV2_ERROR_INVALID_FACT, head, "V2 clause head has inconsistent arity");
    }
    int unified = known && clause.count
        ? ht_unify_instance(m->terms, search->goal, head, clause.values, clause.count)
        : ht_unify(m->terms, search->goal, head);
    if (unified < 0) return fail(m, ht_error(m->terms));
    if (!unified) return 1;
    if (literal) {
        body = clause.body == HT_NONE ? true_term(m) : clause.count ? ht_instantiate(m->terms, clause.body, clause.values, clause.count) : clause.body;
        if (!term_ok(m, body)) return 0;
    }
    Search alternative = *search;
    if (alternative.phase == SEARCH_EQUAL_LOCAL) alternative.fallback = 0;
    if (search_has_alternative(&alternative)) {
        Choice choice = { 0 };
        choice.kind = 1;
        choice.checkpoint = saved;
        choice.search = alternative;
        if (!push_choice(m, choice)) return 0;
    }
    Frame environment = search->frame;
    environment.barrier = search->barrier;
    if (!schedule(m, body, environment, environment.next)) return 0;
    m->current = environment;
    if (m->host_state) event(m, HV2_EVENT_SETTLE, HT_NONE, CONTINUE_WORK, 0);
    return 1;
}

static int unusable_fact(HolV2Machine *m, HTerm fact);

/* goal is the spine of the current goal when the caller has it. */
static int begin_search(HolV2Machine *m, int equality, const HTSpine *goal)
{
    HTSpine spine;
    if (!goal && !normalized_spine(m, m->current.goal, &spine)) return fail(m, ht_error(m->terms));
    HTerm head = goal ? goal->head : spine.head;
    size_t arity = goal ? goal->count : spine.count;
    if (!goal) ht_spine_free(&spine);
    HTView view = ht_view(m->terms, ht_deref(m->terms, head));
    if (view.tag != HT_CONST && view.tag != HT_NOMINAL) return invalid_term(m, HV2_ERROR_INVALID_GOAL, m->current.goal, "Bad V2 goal: predicate head is not rigid");
    size_t newest = m->current.hyps;
    if (newest != NONE && (m->hyps[newest].unusable || m->hyps[newest].undecided)) {
        /* The newest fact that is no clause as the variables are bound now;
            * instantiate_fact reports it. A chain with a fact that was no clause
            * when it came is read whole, and any other chain only at the facts
            * that a later binding can have made such. */
        int certain = m->hyps[newest].unusable;
        size_t h = certain ? newest : m->hyps[newest].undecided - 1;
        while (h != NONE) {
            int unusable = unusable_fact(m, m->hyps[h].fact);
            if (unusable < 0) return 0;
            if (unusable == 1) {
                HTerm clause_head, clause_body;
                if (!instantiate_fact(m, m->hyps[h].fact, m->current.scope, &clause_head, &clause_body)) return 0;
            }
            size_t older = m->hyps[h].next;
            h = certain ? older : older != NONE && m->hyps[older].undecided ? m->hyps[older].undecided - 1 : NONE;
        }
        if (certain) return fail(m, "A V2 hypothesis chain lost its unusable fact");
    }
    if (m->next_call >= INT64_MAX) return fail(m, "V2 call identity exhausted");
    Search search = { 0 };
    search.goal = m->current.goal;
    search.head = head;
    search.arity = arity;
    size_t plain_arity;
    search.plain = rigid_head_of(m, search.goal, &plain_arity) != HT_NONE && plain_arity == search.arity;
    search.global = NONE;
    search.keyed = NONE;
    search.unkeyed = NONE;
    if (view.tag == HT_CONST && view.symbol < m->predicate_count) {
        /* A keyed fact that the index leaves out has a first argument that
            * clashes with the goal's, so head_clash would have skipped it. */
        const Predicate *predicate = &PREDICATE(m, view.symbol);
        Key key = { KEY_NONE, 0, HT_NONE };
        if (search.plain && predicate->kinds && !predicate->mixed && search.arity == predicate->arity) {
            HTerm first = first_argument(m, search.goal, search.arity);
            key = argument_key(m, first);
            if (key.kind == KEY_NONE) {
                /* A first argument that is a redex shows no head. Its head
                    * normal form does, and every candidate is tried against
                    * that form: no trial reduces the argument again. */
                HTerm reduced = ht_normalize(m->terms, first, HT_HNF);
                if (!term_ok(m, reduced)) return 0;
                if (reduced != ht_deref(m->terms, first)) {
                    search.goal = with_first_argument(m, search.goal, search.arity, reduced);
                    if (!term_ok(m, search.goal)) return 0;
                    key = argument_key(m, reduced);
                }
            }
        }
        if ((predicate->kinds == 1 && key.kind == KEY_NATURAL) || (predicate->kinds == 2 && (key.kind == KEY_CONSTANT || key.kind == KEY_NOMINAL))) {
            const Bucket *bucket = key.kind == KEY_NOMINAL ? NULL : find_bucket(m, view.symbol, key);
            if (bucket) search.keyed = bucket->first;
            search.unkeyed = predicate->plain_first;
        } else {
            search.global = predicate->first;
        }
    }
    search.dynamic = m->dynamic_first;
    search.local = m->current.hyps;
    search.local_unknown = NONE;
    search.local_indexed = search.plain;
    if (search.local_indexed && search.local != NONE) {
        size_t root = m->hyps[search.local].index_root;
        search.local = hypothesis_lookup(m, root, hypothesis_key(m, ht_deref(m->terms, head)));
        search.local_unknown = hypothesis_lookup(m, root, (HypKey) { 0, 2 });
    }
    search.barrier = m->choice_count;
    search.frame = m->current;
    search.frame.call = m->next_call++;
    search.phase = equality ? SEARCH_EQUAL_LOCAL : SEARCH_GLOBAL;
    search.fallback = equality != 0;
    search.equality = equality;
    schedule_search(m, search, checkpoint(m));
    return 1;
}

static int backtrack_step(HolV2Machine *m)
{
    m->event_kind = 0;
    m->end_debugged = 0;
    if (m->step_id && (!m->choice_count || m->choices[m->choice_count - 1].serial < m->step_floor)) {
        return event(m, HV2_EVENT_STEP_FAILED, HT_NONE, CONTINUE_WORK, (int64_t) m->step_id);
    }
    if (!m->choice_count) {
        m->exhausted = 1;
        return 0;
    }
    Choice choice = m->choices[--m->choice_count];
    int restored = restore_checkpoint(m, choice.checkpoint);
    if (!release_token(m, 3, choice.checkpoint.host) || !release_token(m, 2, choice.checkpoint.view)) return 0;
    if (!restored) return !m->error[0];
    if (choice.kind == 0) {
        m->work_head = choice.work_head;
        m->action = ACTION_NEXT;
    } else {
        schedule_search(m, choice.search, choice.checkpoint);
    }
    return 1;
}

/* Unknown or computational heads retain ordinary matching, without a hint. */
static HTerm rigid_fact_head(const HolV2Machine *m, HTerm fact)
{
    size_t budget = 128;
    while (budget) {
        size_t arity = 0;
        HTerm first = HT_NONE, head = fact;
        HTView view;
        for (;;) {
            if (!budget) return HT_NONE;
            --budget;
            view = ht_view(m->terms, head);
            if (view.tag != HT_APP) break;
            first = view.b;
            head = view.a;
            ++arity;
        }
        if (view.tag == HT_NOMINAL) return head;
        if (view.tag != HT_CONST) return HT_NONE;
        int operation = role(m, head);
        if ((operation == HV2_PI || operation == HV2_TY_PI) && arity == 1) {
            HTView binder = ht_view(m->terms, first);
            if (binder.tag != HT_LAM) return HT_NONE;
            fact = binder.a;
        } else if (operation == HV2_IF && arity == 2) {
            fact = first;
        } else {
            return head;
        }
    }
    return HT_NONE;
}

/* 1: below its quantifiers the fact is a logical connective other than a
    * conditional, which no goal can use; 0: it is a clause; -1: store error.
    * This is the test of instantiate_fact, made when the fact is assumed: a
    * search under such a fact is an error whatever its goal is, as it is for
    * the reference interpreter. */
/* What the interpreter finds when it instantiates the fact for a goal.
    * 1: no clause: below its quantifiers, each given a variable, it is a
    * connective other than a conditional. 2: its head there is a variable that
    * is unbound now, so a later binding decides. 0: a clause, or a term that
    * matches no goal. -1: store error, or more binders than the work limit.
    * Each turn takes one quantifier or one abstraction off the term, so the
    * turns end with the term, and the answer is of the whole term. The turns
    * are counted against the work limit of the store, as the visits of one
    * traversal are: a term that has more binders than that is an error of
    * its size, and it is never taken for a clause because it was not read
    * to its end. */
static int unusable_fact(HolV2Machine *m, HTerm fact)
{
    /* the variable that a quantifier gave the term below it and that the
        * term has not taken as an abstraction yet */
    size_t given = 0;
    for (uint64_t turns = ht_work_limit(m->terms); ; --turns) {
        if (!turns) {
            if (!m->error[0]) m->error_code = HV2_ERROR_WORK;
            return fail(m, "Native term work limit exceeded: a V2 hypothesis has too many binders") - 1;
        }
        HTSpine spine;
        if (!normalized_spine(m, fact, &spine)) return fail(m, ht_error(m->terms)) - 1;
        HTView head = ht_view(m->terms, ht_deref(m->terms, spine.head));
        int operation = head.tag == HT_CONST ? role(m, spine.head) : HV2_ORDINARY;
        size_t written = spine.count, arity = written + given;
        HTerm first = written ? spine.args[0] : HT_NONE;
        ht_spine_free(&spine);
        if (head.tag == HT_LAM) {
            if (!given) return 0;
            fact = head.a;
            given = 0;
        } else if (head.tag == HT_VAR) {
            return 2;
        } else if (head.tag != HT_CONST) {
            return 0;
        } else if ((operation == HV2_PI || operation == HV2_TY_PI) && arity == 1) {
            /* a quantifier that was itself given the variable has that
                * variable for its body, and a variable of its own is no connective */
            if (!written) return 0;
            fact = first;
            given = 1;
        } else {
            return operation >= HV2_TY_PI && operation <= HV2_IS && !(operation == HV2_IF && arity == 2);
        }
    }
}

typedef struct {
    int operation;
    HTerm head, argument;
    int64_t meta;
    size_t start;
} AssumptionFrame;

typedef struct { HTerm first, *more; size_t count, capacity; } ExpandedAssumptions;

static HTerm *expanded_clause(ExpandedAssumptions *clauses, size_t index)
{
    return index ? &clauses->more[index - 1] : &clauses->first;
}

static int assumption_visit(HolV2Machine *m, uint64_t *remaining)
{
    if (*remaining) { --*remaining; return 1; }
    if (!m->error[0]) m->error_code = HV2_ERROR_WORK;
    return fail(m, "Native term work limit exceeded while expanding a V2 assumption");
}

/* Visit conjunctions left first. A binder or conditional wraps exactly the
    * clauses emitted below it, using the original binder type and metadata. */
static int expand_assumption(HolV2Machine *m, HTerm fact, ExpandedAssumptions *clauses)
{
    AssumptionFrame *pending = NULL;
    size_t depth = 0, capacity = 0;
    uint64_t remaining = ht_work_limit(m->terms);
    int success = 0;
    while (fact != HT_NONE || depth) {
        if (fact == HT_NONE) {
            AssumptionFrame frame = pending[--depth];
            if (frame.operation == HV2_AND) {
                fact = frame.argument;
                continue;
            }
            for (size_t i = frame.start; i < clauses->count; ++i) {
                if (!assumption_visit(m, &remaining)) goto done;
                HTerm *clause = expanded_clause(clauses, i);
                if (frame.operation == HV2_IF) {
                    HTerm partial = ht_app(m->terms, frame.head, *clause, -1);
                    if (!term_ok(m, partial)) goto done;
                    *clause = ht_app(m->terms, partial, frame.argument, -1);
                } else {
                    HTerm binder = ht_lam_typed(m->terms, *clause, frame.meta, frame.argument);
                    if (!term_ok(m, binder)) goto done;
                    *clause = ht_app(m->terms, frame.head, binder, -1);
                }
                if (!term_ok(m, *clause)) goto done;
            }
            continue;
        }
        if (!assumption_visit(m, &remaining)) goto done;
        HTSpine spine;
        if (!normalized_spine(m, fact, &spine)) { fail(m, ht_error(m->terms)); goto done; }
        int operation = role(m, spine.head);
        AssumptionFrame frame = { operation, spine.head, HT_NONE, -1, clauses->count };
        HTerm child = HT_NONE;
        if ((operation == HV2_AND || operation == HV2_IF) && spine.count == 2) {
            child = spine.args[0];
            frame.argument = spine.args[1];
        } else if ((operation == HV2_PI || operation == HV2_TY_PI) && spine.count == 1) {
            HTView binder = ht_view(m->terms, ht_deref(m->terms, spine.args[0]));
            if (binder.tag == HT_LAM) {
                child = binder.a;
                frame.meta = binder.meta;
                frame.argument = binder.b;
            }
        }
        ht_spine_free(&spine);
        if (child != HT_NONE) {
            if (!reserve(m, pending, &capacity, depth + 1, sizeof(*pending))) goto done;
            pending[depth++] = frame;
        } else {
            if (!reserve(m, clauses->more, &clauses->capacity, clauses->count, sizeof(*clauses->more))) goto done;
            *expanded_clause(clauses, clauses->count++) = fact;
        }
        fact = child;
    }
    success = 1;
done:
    hm_free(pending);
    return success;
}

static int enter_implication(HolV2Machine *m, uint64_t premises)
{
    HTSpine spine;
    if (!normalized_spine(m, m->current.goal, &spine)) return fail(m, ht_error(m->terms));
    if (spine.count != 2) { ht_spine_free(&spine); return fail(m, "Malformed V2 implication"); }
    ExpandedAssumptions expanded = { 0 };
    int success = expand_assumption(m, spine.args[0], &expanded);
    size_t hyps = m->current.hyps;
    for (size_t i = expanded.count; success && i > 0; --i) {
        HTerm clause = *expanded_clause(&expanded, i - 1);
        success = reserve(m, m->hyps, &m->hyp_capacity, m->hyp_count + 1, sizeof(*m->hyps));
        if (success) {
            int unusable = unusable_fact(m, clause);
            if (unusable < 0) { success = 0; break; }
            size_t undecided = unusable == 2 ? m->hyp_count + 1 : hyps != NONE ? m->hyps[hyps].undecided : 0;
            m->hyps[m->hyp_count] = (Hypothesis) { clause, rigid_fact_head(m, clause), hyps, NONE, NONE, 0, unusable == 1 || (hyps != NONE && m->hyps[hyps].unusable), undecided };
            success = index_hypothesis(m, m->hyp_count, 1);
            if (!success) break;
            hyps = m->hyp_count++;
            if (m->arena_spent != SIZE_MAX) ++m->arena_spent;
        }
    }
    if (success) {
        Frame inside = m->current;
        inside.hyps = hyps;
        inside.premises = premises;
        success = schedule(m, spine.args[1], inside, m->current.next);
    }
    hm_free(expanded.more);
    ht_spine_free(&spine);
    return success;
}

/* 1: the host would leave the equality to the search without reading a state;
    * 0: the host decides; -1: store error. */
static int plain_equality(HolV2Machine *m, const HTSpine *spine)
{
    HTerm type = ht_normalize(m->terms, spine->args[0], HT_HNF);
    if (type == HT_NONE) return -1;
    if (role(m, type) == HV2_NATURAL) return 0;
    for (size_t i = 1; i < 3; ++i) {
        int arithmetic = ht_mentions_arithmetic(m->terms, spine->args[i]);
        if (arithmetic) return arithmetic < 0 ? -1 : 0;
    }
    return 1;
}

/* 1: the antecedent is a conjunction of atoms and clauses with ordinary heads,
    * to which the host would add no premise; 0: the host decides; -1: store error. */
static int plain_antecedent(HolV2Machine *m, HTerm fact, size_t depth, uint64_t *remaining)
{
    HTSpine spine;
    if (depth > 64) return 0;
    if (!assumption_visit(m, remaining)) return -1;
    if (!normalized_spine(m, fact, &spine)) return -1;
    int tag = ht_view(m->terms, ht_deref(m->terms, spine.head)).tag;
    int operation = role(m, spine.head);
    int plain = tag == HT_NOMINAL || (tag == HT_CONST && (operation == HV2_ORDINARY || operation == HV2_IF));
    if (tag == HT_CONST && operation == HV2_AND && spine.count == 2) {
        plain = plain_antecedent(m, spine.args[0], depth + 1, remaining);
        if (plain == 1) plain = plain_antecedent(m, spine.args[1], depth + 1, remaining);
    }
    ht_spine_free(&spine);
    return plain;
}

static int execute_current(HolV2Machine *m)
{
    HTSpine spine;
    if (!normalized_spine(m, m->current.goal, &spine)) return fail(m, ht_error(m->terms));
    int operation = role(m, spine.head);
    size_t arity = spine.count;
    int success = 1;
    m->action = ACTION_NEXT;
    switch (operation) {
        case HV2_TRUE:
            if (arity) success = invalid_term(m, HV2_ERROR_INVALID_GOAL, m->current.goal, "Malformed V2 true goal");
            break;
        case HV2_FAIL:
            if (arity) invalid_term(m, HV2_ERROR_INVALID_GOAL, m->current.goal, "Malformed V2 fail goal");
            success = 0;
            break;
        case HV2_CUT:
            if (arity) success = invalid_term(m, HV2_ERROR_INVALID_GOAL, m->current.goal, "Malformed V2 cut goal");
            else if (m->current.barrier > m->choice_count) success = fail(m, "Invalid V2 cut activation");
            else while (m->choice_count > m->current.barrier) {
                Choice *choice = &m->choices[--m->choice_count];
                if (!release_token(m, 3, choice->checkpoint.host) || !release_token(m, 2, choice->checkpoint.view)) { success = 0; break; }
            }
            break;
        case HV2_AND:
            if (arity != 2) success = invalid_term(m, HV2_ERROR_INVALID_GOAL, m->current.goal, "Malformed V2 conjunction");
            else {
                Frame right = m->current;
                right.goal = spine.args[1];
                right.next = m->current.next;
                size_t continuation = push_frame(m, right);
                success = continuation != NONE && schedule(m, spine.args[0], m->current, continuation);
            }
            break;
        case HV2_OR:
            if (arity != 2) success = invalid_term(m, HV2_ERROR_INVALID_GOAL, m->current.goal, "Malformed V2 disjunction");
            else {
                Frame right = m->current;
                right.goal = spine.args[1];
                right.next = m->current.next;
                size_t alternative = push_frame(m, right);
                Choice choice = { 0 };
                choice.kind = 0;
                choice.checkpoint = checkpoint(m);
                choice.work_head = alternative;
                success = alternative != NONE && push_choice(m, choice) && schedule(m, spine.args[0], m->current, m->current.next);
            }
            break;
        case HV2_PI:
        case HV2_SIGMA:
            if (arity != 1 || (operation == HV2_PI && m->current.scope == SIZE_MAX)) success = invalid_term(m, HV2_ERROR_INVALID_GOAL, m->current.goal, "Malformed V2 quantifier");
            else {
                HTerm callable = ht_normalize(m->terms, spine.args[0], HT_HNF);
                if (!term_ok(m, callable)) { success = 0; break; }
                HTView function = ht_view(m->terms, callable);
                int64_t meta = function.tag == HT_LAM ? function.meta : -1;
                size_t scope = m->current.scope + (operation == HV2_PI);
                HTerm type = function.tag == HT_LAM ? function.b : HT_NONE;
                HTerm binder = operation == HV2_PI ? ht_nominal_typed(m->terms, scope, meta, type) : ht_var_typed(m->terms, scope, 0, meta, type);
                HTerm goal = ht_apply(m->terms, callable, binder);
                Frame inside = m->current;
                inside.scope = scope;
                success = term_ok(m, binder) && term_ok(m, goal) && schedule(m, goal, inside, m->current.next);
            }
            break;
        case HV2_IMPLY:
            if (arity != 2) success = invalid_term(m, HV2_ERROR_INVALID_GOAL, m->current.goal, "Malformed V2 implication");
            else {
                uint64_t remaining = ht_work_limit(m->terms);
                int plain = plain_antecedent(m, spine.args[0], 0, &remaining);
                if (plain < 0) success = fail(m, ht_error(m->terms));
                else if (plain) success = enter_implication(m, m->current.premises);
                else success = event(m, HV2_EVENT_IMPLY, spine.args[0], CONTINUE_IMPLY, 0);
            }
            break;
        case HV2_EQ:
            if (arity != 3) success = invalid_term(m, HV2_ERROR_INVALID_GOAL, m->current.goal, "Malformed V2 equality");
            else {
                int plain = plain_equality(m, &spine);
                if (plain < 0) success = fail(m, ht_error(m->terms));
                else if (plain) success = begin_search(m, 4, &spine);
                else success = event(m, HV2_EVENT_EQUALITY, m->current.goal, CONTINUE_EQUALITY, 0);
            }
            break;
        case HV2_SAME:
            if (arity != 3) success = invalid_term(m, HV2_ERROR_INVALID_GOAL, m->current.goal, "Malformed V2 term identity");
            else {
                int same = ht_same(m->terms, spine.args[1], spine.args[2]);
                success = same < 0 ? fail(m, ht_error(m->terms)) : same;
            }
            break;
        case HV2_IS:
        case HV2_LE:
        case HV2_LT:
        case HV2_GE:
        case HV2_GT:
        case HV2_READ:
        case HV2_PRINT:
        case HV2_DEBUG:
        case HV2_PRESBURGER:
        case HV2_ORACLE:
            success = event(m, HV2_EVENT_PRIMITIVE, m->current.goal, CONTINUE_WORK, 0);
            break;
        case HV2_FLEX:
            /* arguments: the type instance, then the term */
            if (arity != 2) success = invalid_term(m, HV2_ERROR_INVALID_GOAL, m->current.goal, "Malformed V2 flex goal");
            else {
                int flexible = flexible_head(m, spine.args[1]);
                success = flexible < 0 ? fail(m, ht_error(m->terms)) : flexible;
            }
            break;
        case HV2_TY_PI:
        case HV2_IF:
            success = invalid_term(m, HV2_ERROR_INVALID_GOAL, m->current.goal, "A V2 clause operator appeared as a goal");
            break;
        default:
            success = begin_search(m, 0, &spine);
            break;
    }
    ht_spine_free(&spine);
    return success;
}

static int valid_index(int64_t index, size_t limit)
{
    return index >= 0 && (uint64_t) index < limit;
}

static int valid_meta(int64_t meta, size_t count)
{
    return meta == -1 || valid_index(meta, count);
}

static void *copy_array(HMemory *memory, const void *source, size_t count, size_t width)
{
    if (!count) return NULL;
    if (count > SIZE_MAX / width) return NULL;
    void *copy = hm_alloc(memory, count * width);
    if (copy) memcpy(copy, source, count * width);
    return copy;
}

static _Atomic uint64_t next_origin = 1;

/* A role of a constructor of types. */
static int type_role(int operation)
{
    return operation == HV2_TYPE || operation == HV2_NATURAL || operation == HV2_ARROW;
}

static int set_symbol_role(HolV2Machine *m, size_t symbol, int operation)
{
    if (operation == HV2_PRESBURGER && !ht_set_opaque_symbol(m->terms, symbol)) return fail(m, ht_error(m->terms));
    if (operation == HV2_ARITHMETIC && !ht_set_arithmetic_symbol(m->terms, symbol)) return fail(m, ht_error(m->terms));
    if (operation == HV2_SUCCESSOR && !ht_set_successor(m->terms, symbol)) return fail(m, ht_error(m->terms));
    if (type_role(operation) && !ht_set_type_symbol(m->terms, symbol)) return fail(m, ht_error(m->terms));
    if (operation == HV2_ARROW) ht_set_arrow(m->terms, symbol);
    return 1;
}

/* Restore retains the live vocabulary even after a machine error. Publish a
    * role and its term summaries together. The common single ordinary append
    * already rolls back its logical length if vector allocation fails. */
static int append_symbol_role(HolV2Machine *m, size_t symbol, int operation)
{
    int64_t role = operation;
    if (symbol == m->symbol_count && operation != HV2_PRESBURGER && operation != HV2_ARITHMETIC
        && operation != HV2_SUCCESSOR && !type_role(operation)) {
        if (!program_append(m, TABLE_ROLES, &role)) return 0;
        ++m->symbol_count;
        return 1;
    }
    HvVector pending;
    hv_clone(&pending, &m->program[TABLE_ROLES], m->memory);
    while (pending.count <= symbol) {
        int64_t next = pending.count == symbol ? role : HV2_ORDINARY;
        if (!hv_append(&pending, &next)) {
            hv_destroy(&pending);
            return fail(m, "V2 program append allocation failed");
        }
    }
    if (!set_symbol_role(m, symbol, operation)) {
        hv_destroy(&pending);
        return 0;
    }
    hv_destroy(&m->program[TABLE_ROLES]);
    m->program[TABLE_ROLES] = pending;
    m->symbol_count = symbol + 1;
    return 1;
}

static int add_symbols(HolV2Machine *m, const int64_t *roles, size_t total)
{
    for (size_t first = m->symbol_count, i = first; i < total; ++i) {
        int64_t operation = roles[i - first];
        if (operation < HV2_ORDINARY || operation > HV2_TYPE) return fail(m, "Invalid V2 symbol role");
        if (operation == HV2_SUCCESSOR && m->truth != HT_NONE) return fail(m, "A V2 fragment declares another successor symbol");
        if (!append_symbol_role(m, i, (int) operation)) return 0;
    }
    return 1;
}

static int grow_predicates(HolV2Machine *m, size_t count)
{
    Predicate empty = { NONE, NONE, NONE, NONE, NONE, 0, 0 };
    while (m->predicate_count < count) {
        if (!program_append(m, TABLE_PREDICATES, &empty)) return 0;
        ++m->predicate_count;
    }
    return 1;
}

static StringLiteral *find_string(StringLiteral *literals, size_t capacity, StringLiteral key)
{
    uint64_t hash = ((uint64_t) key.offset + 1) * UINT64_C(0x9E3779B97F4A7C15) ^ ((uint64_t) key.length + UINT64_C(0x632BE59BD9B4E019));
    hash = (hash ^ (hash >> 30) ^ key.cons) * UINT64_C(0xBF58476D1CE4E5B9);
    hash = (hash ^ (hash >> 27) ^ key.nil) * UINT64_C(0x94D049BB133111EB);
    hash ^= (hash >> 31) ^ key.type;
    for (size_t at = (size_t) hash & (capacity - 1);; at = (at + 1) & (capacity - 1)) {
        StringLiteral *literal = &literals[at];
        if (!literal->buffer || (literal->offset == key.offset && literal->length == key.length && literal->cons == key.cons && literal->nil == key.nil && literal->type == key.type)) return literal;
    }
}

/* The place of a literal in the cache: its entry, or the empty one that
    * waits for its buffer. NULL: allocation failure. */
static StringLiteral *string_slot(HolV2Machine *m, StringCache *cache, StringLiteral key)
{
    if (cache->count >= cache->capacity / 2) {
        size_t capacity = cache->capacity ? cache->capacity * 2 : 32;
        StringLiteral *literals = capacity > cache->capacity && capacity <= SIZE_MAX / sizeof(*literals) ? hm_calloc(m->memory, capacity, sizeof(*literals)) : NULL;
        if (!literals) {
            fail(m, "V2 string cache allocation failed");
            return NULL;
        }
        for (size_t i = 0; i < cache->capacity; ++i) {
            StringLiteral literal = cache->literals[i];
            if (literal.buffer) *find_string(literals, capacity, literal) = literal;
        }
        hm_free(cache->literals);
        cache->literals = literals;
        cache->capacity = capacity;
    }
    return find_string(cache->literals, cache->capacity, key);
}

static void free_strings(StringCache *cache)
{
    for (size_t i = 0; i < cache->capacity; ++i) ht_string_release(cache->literals[i].buffer);
    hm_free(cache->literals);
    hm_free(cache->prefixes);
}

/* Whether the template is an ordinary constant applied to an ordinary
    * constant or to a constructor of types, as the constructors of a compiled
    * string are: `cons char`. */
static int typed_constant(const HolV2Machine *m, HTerm term, size_t *function, size_t *argument)
{
    HTView application = ht_view(m->terms, term);
    if (application.tag != HT_APP) return 0;
    HTView f = ht_view(m->terms, application.a), x = ht_view(m->terms, application.b);
    int argument_role = role(m, application.b);
    if (f.tag != HT_CONST || x.tag != HT_CONST || role(m, application.a) != HV2_ORDINARY || (argument_role != HV2_ORDINARY && argument_role != HV2_TYPE)) return 0;
    *function = f.symbol;
    *argument = x.symbol;
    return 1;
}

/* The list of a pooled string. Its cells are string cells when its
    * constructors have the shape of a compiled string; a native descriptor of
    * another shape gets the same list of plain applications. */
static HTerm string_template(HolV2Machine *m, const int64_t *row, size_t at, const HTerm *roots, const int64_t *payload, size_t remaining, StringCache *cache)
{
    if (!valid_index(row[1], at) || !valid_index(row[2], at) || row[3] < 0 || row[4] < 0 || (uint64_t) row[3] > remaining || (uint64_t) row[4] > remaining - (size_t) row[3]) {
        fail(m, "Invalid V2 pooled string template");
        return HT_NONE;
    }
    HTerm value = roots[row[2]];
    if (!row[4]) return value;
    size_t offset = (size_t) row[3], length = (size_t) row[4];
    for (size_t i = 0; i < length; ++i) {
        int64_t symbol = payload[offset + i];
        if (!valid_index(symbol, m->symbol_count) || ROLE(m, symbol) != HV2_ORDINARY) {
            fail(m, "Invalid V2 string character symbol");
            return HT_NONE;
        }
    }
    if (!cache->prefixes) {
        if (m->symbol_count > SIZE_MAX / sizeof(*cache->prefixes) || !(cache->prefixes = hm_calloc(m->memory, m->symbol_count, sizeof(*cache->prefixes)))) {
            fail(m, "V2 string prefix allocation failed");
            return HT_NONE;
        }
    }
    HTStringBuffer *buffer = NULL;
    StringLiteral key = { offset, length, 0, 0, 0, NULL };
    size_t type;
    if (typed_constant(m, roots[row[1]], &key.cons, &key.type) && typed_constant(m, value, &key.nil, &type) && type == key.type) {
        StringLiteral *literal = string_slot(m, cache, key);
        if (!literal) return HT_NONE;
        if (!literal->buffer) {
            key.buffer = ht_string_buffer(m->terms, key.cons, key.nil, key.type, payload + offset, length);
            if (!key.buffer) return HT_NONE;
            *literal = key;
            ++cache->count;
        }
        buffer = literal->buffer;
    }
    for (size_t i = length; i > 0; --i) {
        int64_t symbol = payload[offset + i - 1];
        StringPrefix *prefix = &cache->prefixes[symbol];
        /* Another occurrence can have different metadata and typed cons. */
        if (prefix->stamp != at + 1) {
            HTerm character = ht_constant(m->terms, (size_t) symbol, row[5]);
            if (character == HT_NONE) return HT_NONE;
            prefix->head = ht_app(m->terms, roots[row[1]], character, row[5]);
            if (prefix->head == HT_NONE) return HT_NONE;
            prefix->stamp = at + 1;
        }
        value = buffer ? ht_string_cell(m->terms, prefix->head, value, row[5], buffer, i - 1) : ht_app(m->terms, prefix->head, value, row[5]);
        if (value == HT_NONE) return HT_NONE;
    }
    return value;
}

static HTerm template_term(HolV2Machine *m, int64_t version, const int64_t *row, size_t at, const HTerm *roots, const int64_t *digits, size_t remaining, StringCache *strings)
{
    if ((row[0] != 7 && (row[3] || row[4])) || !valid_meta(row[5], m->meta_count)) {
        fail(m, "Invalid V2 template metadata or reserved operand");
        return HT_NONE;
    }
    HTerm value = HT_NONE;
    switch (row[0]) {
        case 0:
            if (valid_index(row[1], m->query_count) && row[2] == 0) value = m->query[row[1]];
            break;
        case 1:
            if (valid_index(row[1], m->symbol_count) && row[2] == 0) value = ht_constant(m->terms, (size_t) row[1], row[5]);
            break;
        case 2:
            if (valid_index(row[1], at) && valid_index(row[2], at)) value = ht_app(m->terms, roots[row[1]], roots[row[2]], row[5]);
            break;
        case 3:
            if (row[1] >= 0 && (uint64_t) row[1] <= SIZE_MAX && row[2] == 0) value = ht_index(m->terms, (size_t) row[1]);
            break;
        case 4:
            if (valid_index(row[1], at) && (row[2] == 0 || (version >= 4 && row[2] > 0 && valid_index(row[2] - 1, at)))) {
                value = ht_lam_typed(m->terms, roots[row[1]], row[5], row[2] ? roots[row[2] - 1] : HT_NONE);
            }
            break;
        case 5:
            if (row[1] >= 0 && row[2] > 0 && (uint64_t) row[1] <= remaining && (uint64_t) row[2] <= remaining - (size_t) row[1]) {
                size_t n = (size_t) row[2];
                char *text = n < SIZE_MAX ? hm_alloc(m->memory, n + 1) : NULL;
                if (!text) { fail(m, "V2 natural allocation failed"); break; }
                int valid = 1;
                for (size_t j = 0; j < n; ++j) {
                    int64_t ch = digits[(size_t) row[1] + j];
                    if (ch < '0' || ch > '9') valid = 0;
                    text[j] = (char) ch;
                }
                text[n] = '\0';
                if (valid && (n == 1 || text[0] != '0')) value = ht_nat(m->terms, text);
                hm_free(text);
            }
            break;
        case 6:
            if (!row[1] && !row[2]) value = ht_wildcard(m->terms);
            break;
        case 7:
            if (version >= 3) value = string_template(m, row, at, roots, digits, remaining, strings);
            break;
        default:
            break;
    }
    if (value == HT_NONE) {
        const char *message = ht_error(m->terms);
        fail(m, message && message[0] ? message : "Invalid V2 term template");
    }
    return value;
}

/* Reads one wordcode fragment. LOAD_CREATE and LOAD_EXTEND add it to the
    * program; LOAD_QUERY builds it above the program, for one run. */
static int load(HolV2Machine *m, const int64_t *code, size_t length, int mode)
{
    size_t old_meta = m->meta_count;
    if (!code || length < 8 || code[0] != MAGIC || (code[1] < 2 || code[1] > 6)) return fail(m, "Invalid V2 wordcode header");
    for (size_t i = 2; i < 8; ++i) {
        if (i == 6 && mode == LOAD_EXTEND) continue;
        if (code[i] < 0 || (uint64_t) code[i] > SIZE_MAX) return fail(m, "Invalid V2 wordcode count");
    }
    size_t term_count = (size_t) code[2], symbol_total = (size_t) code[3], fact_count = (size_t) code[4], query_count = (size_t) code[5];
    if (symbol_total < m->symbol_count) return fail(m, "V2 wordcode has fewer symbols than its machine");
    if (mode == LOAD_EXTEND && (query_count || code[6] != -1)) return fail(m, "A V2 program fragment has a query");
    if (mode == LOAD_QUERY && fact_count) return fail(m, "A V2 query fragment has clauses");
    size_t symbol_count = symbol_total - m->symbol_count;
    size_t remaining = length - 8;
    size_t query_width = code[1] >= 5 ? 3 : 2;
    if (query_count > remaining / query_width) return fail(m, "Truncated V2 query table");
    const int64_t *queries = code + 8;
    remaining -= query_width * query_count;
    if (symbol_count > remaining) return fail(m, "Truncated V2 symbol table");
    const int64_t *roles = queries + query_width * query_count;
    remaining -= symbol_count;
    if (term_count > remaining / 6) return fail(m, "Truncated V2 template table");
    const int64_t *templates = roles + symbol_count;
    remaining -= term_count * 6;
    if (fact_count > remaining / 2) return fail(m, "Truncated V2 clause table");
    const int64_t *facts = templates + term_count * 6;
    remaining -= fact_count * 2;
    const int64_t *digits = facts + fact_count * 2;
    if (mode != LOAD_EXTEND && !valid_index(code[6], term_count)) return fail(m, "Invalid V2 query root");
    m->meta_count = (size_t) code[7];
    if (!add_symbols(m, roles, symbol_total)) return 0;
    if (mode == LOAD_CREATE) {
        int has_true = 0, has_successor = 0;
        for (size_t i = 0; i < m->symbol_count; ++i) {
            if (ROLE(m, i) == HV2_TRUE) has_true = 1;
            if (ROLE(m, i) == HV2_SUCCESSOR) has_successor = 1;
        }
        if (!has_true || !has_successor) return fail(m, "V2 requires true and successor symbols");
        m->truth = true_term(m);
        if (!term_ok(m, m->truth)) return 0;
    }
    if (query_count > SIZE_MAX / sizeof(*m->query)) return fail(m, "V2 query allocation overflow");
    m->query = query_count ? hm_calloc(m->memory, query_count, sizeof(*m->query)) : NULL;
    if (query_count && !m->query) return fail(m, "V2 query allocation failed");
    HTerm *roots = term_count <= SIZE_MAX / sizeof(*roots) ? hm_alloc(m->memory, (term_count ? term_count : 1) * sizeof(*roots)) : NULL;
    if (!roots) return fail(m, "V2 template allocation failed");
    StringCache strings = { 0 };
    for (size_t i = 0; i < term_count; ++i) roots[i] = HT_NONE;
    for (size_t i = 0; !m->error[0] && i < term_count; ++i) {
        const int64_t *row = templates + 6 * i;
        int open = row[0] == 0;
        if (row[0] == 2 || row[0] == 7) open = !valid_index(row[1], i) || !valid_index(row[2], i) || roots[row[1]] == HT_NONE || roots[row[2]] == HT_NONE;
        if (row[0] == 4) open = !valid_index(row[1], i) || roots[row[1]] == HT_NONE || (row[2] > 0 && (!valid_index(row[2] - 1, i) || roots[row[2] - 1] == HT_NONE));
        if (!open) roots[i] = template_term(m, code[1], row, i, roots, digits, remaining, &strings);
    }
    for (size_t i = 0; i < query_count; ++i) {
        const int64_t *query = queries + query_width * i;
        if ((query[0] != 0 && query[0] != 1) || !valid_meta(query[1], m->meta_count)) { fail(m, "Invalid V2 query descriptor"); break; }
        if (query_width == 3 && query[2] != -1 && (query[0] || !valid_index(query[2], term_count))) { fail(m, "Invalid V2 query type descriptor"); break; }
        m->query[i] = ht_var(m->terms, 0, (int) query[0], query[1]);
        m->query_count = i + 1;
        if (!term_ok(m, m->query[i])) break;
    }
    for (size_t i = 0; !m->error[0] && i < term_count; ++i) {
        if (roots[i] == HT_NONE) roots[i] = template_term(m, code[1], templates + 6 * i, i, roots, digits, remaining, &strings);
    }
    for (size_t i = 0; !m->error[0] && query_width == 3 && i < query_count; ++i) {
        int64_t type = queries[query_width * i + 2];
        if (type != -1 && !ht_set_initial_type(m->terms, m->query[i], roots[type])) fail(m, ht_error(m->terms));
    }
    free_strings(&strings);
    if (!m->error[0] && fact_count) {
        if (fact_count > SIZE_MAX - m->fact_count) fail(m, "V2 fact allocation overflow");
        else grow_predicates(m, m->symbol_count);
    }
    for (size_t i = 0; !m->error[0] && i < fact_count; ++i) {
        int64_t symbol = facts[2 * i], root = facts[2 * i + 1];
        if ((symbol != -1 && !valid_index(symbol, m->symbol_count)) || !valid_index(root, term_count)) fail(m, "Invalid V2 fact descriptor");
        else {
            Fact fact = { symbol, roots[root], NONE, NONE, HT_NONE, HT_NONE, HT_NONE, 0, 0, 0, 0 };
            if (program_append(m, TABLE_FACTS, &fact)) index_fact(m, m->fact_count++);
        }
    }
    if (!m->error[0] && mode != LOAD_EXTEND) {
        Frame initial = { roots[code[6]], NONE, 0, NONE, 0, 0, 0 };
        m->work_head = push_frame(m, initial);
        m->current = initial;
        m->exhausted = 0;
    }
    if (mode != LOAD_QUERY) {
        m->permanent = ht_heap_count(m->terms);
        m->idle_uid = ht_next_uid(m->terms);
        m->program_symbols = m->symbol_count;
        m->program_meta = m->meta_count;
        if (!m->error[0]) { ht_seal(m->terms); if (ht_error(m->terms)[0]) fail(m, ht_error(m->terms)); }
    }
    hol_v2_set_collection_step(m, 65536);
    hm_free(roots);
    if (!m->error[0] && (mode == LOAD_CREATE || (mode == LOAD_EXTEND && (term_count || symbol_count || fact_count || old_meta != m->meta_count)))) advance_version(m);
    return !m->error[0];
}

HolV2Machine *hol_v2_create_limited(const int64_t *code, size_t length, uint64_t limit, int *error_code)
{
    if (error_code) *error_code = HV2_ERROR_NONE;
    if (limit > SIZE_MAX) { if (error_code) *error_code = HV2_ERROR_USAGE; return NULL; }
    HMemory *memory = hm_create();
    if (!memory) { if (error_code) *error_code = HV2_ERROR_ALLOCATION; return NULL; }
    atomic_store_explicit(&memory->limit, (size_t) limit, memory_order_relaxed);
    HolV2Machine *m = hm_calloc(memory, 1, sizeof(*m));
    if (!m) {
        if (error_code) *error_code = atomic_load_explicit(&memory->fault, memory_order_relaxed) == 1 ? HV2_ERROR_MEMORY : HV2_ERROR_ALLOCATION;
        hm_release(memory);
        return NULL;
    }
    m->memory = memory;
    hv_init(&m->program[TABLE_ROLES], memory, sizeof(int64_t), copy_role, NULL);
    hv_init(&m->program[TABLE_FACTS], memory, sizeof(Fact), copy_fact, NULL);
    hv_init(&m->program[TABLE_PREDICATES], memory, sizeof(Predicate), copy_predicate, NULL);
    hv_init(&m->program[TABLE_BUCKETS], memory, sizeof(Bucket), copy_bucket, NULL);
    m->work_head = NONE;
    m->dynamic_first = NONE;
    m->dynamic_last = NONE;
    m->truth = HT_NONE;
    m->next_call = 1;
    m->origin = atomic_fetch_add(&next_origin, 1);
    m->engine_origin = m->origin;
    if (!m->origin) { fail(m, "V2 runtime identity exhausted"); if (error_code) *error_code = hol_v2_error_code(m); return m; }
    m->terms = ht_create_in(m->memory);
    if (!m->terms) { fail(m, "V2 term store allocation failed"); if (error_code) *error_code = hol_v2_error_code(m); return m; }
    load(m, code, length, LOAD_CREATE);
    if (error_code) *error_code = hol_v2_error_code(m);
    return m;
}

HolV2Machine *hol_v2_create(const int64_t *code, size_t length)
{
    return hol_v2_create_limited(code, length, 0, NULL);
}

static void *release_spare(void *data, size_t *capacity, size_t limit)
{
    if (*capacity > limit) {
        hm_free(data);
        data = NULL;
        *capacity = 0;
    }
    return data;
}

/* Leaves the run. The program stays; everything else is as a machine created
    * from that program alone would have it, so the next run numbers its
    * variables, calls and host states from the same origin. A snapshot of the
    * run that was left can no longer be restored. */
static int leave_run(HolV2Machine *m)
{
    if (m->error[0]) return 0;
    if (!ht_reset(m->terms, m->permanent, m->idle_uid, m->program_symbols)) return fail(m, ht_error(m->terms));
    if (!hv_truncate(&m->program[TABLE_ROLES], m->program_symbols)) return fail(m, "V2 symbol truncate allocation failed");
    m->symbol_count = m->program_symbols;
    m->meta_count = m->program_meta;
    for (size_t i = 0; i < m->assignment_count; ++i) hm_free(m->assignments[i].wire);
    m->assignment_count = 0;
    m->assignment_trail = 0;
    m->assignment_heap = 0;
    m->assignment_settled = 1;
    m->assignment_dirty = 0;
    m->settle_action = ACTION_NEXT;
    hm_free(m->query);
    m->query = NULL;
    m->query_count = 0;
    m->work_count = 0;
    m->hyp_count = 0;
    m->hyp_index_count = 0;
    m->choice_count = 0;
    m->next_choice = 0;
    m->step_floor = 0;
    m->step_id = 0;
    m->buffer_count = 0;
    m->work_head = NONE;
    memset(&m->search, 0, sizeof(m->search));
    memset(&m->search_checkpoint, 0, sizeof(m->search_checkpoint));
    m->current = (Frame) { HT_NONE, NONE, 0, NONE, 0, 0, 0 };
    m->batch = 0;
    m->collections = 0;
    m->arena_spent = 0;
    m->host_state = 0;
    m->view_token = 0;
    m->last_view_token = 0;
    m->view_trail = 0;
    m->service_deltas = 0;
    m->transient_output = 0;
    m->scoped_exports = 0;
    m->focused = 0;
    m->focus_count = 0;
    hm_free(m->focus);
    m->focus = NULL;
    clear_host_roots(m);
    m->retired_count = 0;
    m->next_call = 1;
    m->action = ACTION_NEXT;
    m->debugging = 0;
    m->assignment_failed = 0;
    m->exhausted = 1;
    m->answer_ready = 0;
    m->resume_answer = 0;
    m->end_debugged = 0;
    m->event_kind = 0;
    m->event_continuation = 0;
    m->event_aux = 0;
    m->event_term = HT_NONE;
    m->api_code = HV2_ERROR_NONE; m->api_error = NULL;
    m->origin = atomic_fetch_add(&next_origin, 1);
    if (!m->origin) return fail(m, "V2 runtime identity exhausted");
    m->work = release_spare(m->work, &m->work_capacity, 4096);
    m->hyps = release_spare(m->hyps, &m->hyp_capacity, 4096);
    m->hyp_index = release_spare(m->hyp_index, &m->hyp_index_capacity, 4096);
    m->choices = release_spare(m->choices, &m->choice_capacity, 4096);
    m->buffer = release_spare(m->buffer, &m->buffer_capacity, 4096);
    m->assignments = release_spare(m->assignments, &m->assignment_capacity, 4096);
    hol_v2_set_collection_step(m, 65536);
    return 1;
}

int hol_v2_extend(HolV2Machine *m, const int64_t *code, size_t length)
{
    if (!m || m->error[0]) return -1;
    HolV2Machine *next = clone_in(m, m->memory);
    if (!next) {
        int fault = atomic_load_explicit(&m->memory->fault, memory_order_relaxed);
        return api_failure(m, fault == 1 ? HV2_ERROR_MEMORY : HV2_ERROR_ALLOCATION, "V2 program extension allocation failed");
    }
    if (!leave_run(next) || !load(next, code, length, LOAD_EXTEND)) {
        int result = api_failure(m, hol_v2_error_code(next), hol_v2_error(next));
        hol_v2_destroy(next);
        return result;
    }
    if (next->version == m->version) {
        hol_v2_destroy(next);
        m->api_code = HV2_ERROR_NONE;
        m->api_error = NULL;
        return 1;
    }
    release_fields(m);
    *m = *next;
    if (next->api_error == next->api_message) m->api_error = m->api_message;
    hm_free(next);
    hm_release(m->memory);
    return 1;
}

int hol_v2_query(HolV2Machine *m, const int64_t *code, size_t length)
{
    return m && leave_run(m) && load(m, code, length, LOAD_QUERY) ? 1 : -1;
}

int hol_v2_idle(HolV2Machine *m)
{
    return m && leave_run(m) ? 1 : -1;
}

typedef struct {
    HolV2Machine *machine;
    unsigned char *frames, *hyps;
    size_t *frame_forward, *hyp_forward;
    BucketIndex **root_seen;
    size_t root_seen_count, root_seen_capacity;
} Collection;

static void keep_hyps(Collection *c, size_t at)
{
    for (; at != NONE && !c->hyps[at]; at = c->machine->hyps[at].next) c->hyps[at] = 1;
}

static void keep_frames(Collection *c, size_t at)
{
    for (; at != NONE && !c->frames[at]; at = c->machine->work[at].next) {
        c->frames[at] = 1;
        keep_hyps(c, c->machine->work[at].hyps);
    }
}

/* Several retained tokens can share almost their whole persistent UID set.
    * Mark each physical set node once, without writing caches into shared
    * immutable nodes or repeating each old version's complete traversal. */
static size_t root_pointer_slot(BucketIndex **nodes, size_t capacity, BucketIndex *node)
{
    uintptr_t hash = (uintptr_t) node;
    hash ^= hash >> 17;
    hash *= (uintptr_t) UINT64_C(0x9e3779b97f4a7c15);
    size_t at = (size_t) hash & (capacity - 1);
    while (nodes[at] && nodes[at] != node) at = (at + 1) & (capacity - 1);
    return at;
}

static int visit_root(Collection *c, BucketIndex *node)
{
    if (c->root_seen_capacity) {
        size_t at = root_pointer_slot(c->root_seen, c->root_seen_capacity, node);
        if (c->root_seen[at]) return 0;
    }
    if (c->root_seen_count >= c->root_seen_capacity / 2) {
        size_t capacity = c->root_seen_capacity ? c->root_seen_capacity * 2 : 128;
        if (capacity < c->root_seen_capacity || capacity > SIZE_MAX / sizeof(*c->root_seen)) {
            fail(c->machine, "Host root collection index overflow"); return -1;
        }
        BucketIndex **nodes = hm_calloc(c->machine->memory, capacity, sizeof(*nodes));
        if (!nodes) { fail(c->machine, "Host root collection index allocation failed"); return -1; }
        for (size_t i = 0; i < c->root_seen_capacity; ++i) {
            BucketIndex *old = c->root_seen[i];
            if (old) nodes[root_pointer_slot(nodes, capacity, old)] = old;
        }
        hm_free(c->root_seen);
        c->root_seen = nodes;
        c->root_seen_capacity = capacity;
    }
    c->root_seen[root_pointer_slot(c->root_seen, c->root_seen_capacity, node)] = node;
    ++c->root_seen_count;
    hm_count(c->machine->memory, HM_GC_VISITS, 1);
    return 1;
}

static void mark_host_roots(Collection *c, HTCollection *terms, int kind, uint64_t token)
{
    HolV2Machine *m = c->machine;
    if (!token || !m->host_roots_capacity) return;
    HostRoots *roots = &m->host_roots[root_slot(m->host_roots, m->host_roots_capacity, kind, token)];
    if (!roots->token || roots->live) return;
    roots->live = 1;
    BucketIndex *stack[65], *node = roots->set;
    size_t count = 0;
    while (node) {
        int visited = visit_root(c, node);
        if (visited < 0) return;
        if (!visited) { node = count ? stack[--count] : NULL; continue; }
        if (node->bit != NONE) {
            stack[count++] = node->value.children[1];
            node = node->value.children[0];
            continue;
        }
        HTerm term = ht_lookup_uid(m->terms, (uint64_t) node->value.bucket);
        if (term == HT_NONE) { fail(m, "Live host token refers to an expired identity"); return; }
        ht_collect_mark(terms, term);
        node = count ? stack[--count] : NULL;
    }
}

static void collect_mark(HTCollection *terms, void *context)
{
    Collection *c = context;
    HolV2Machine *m = c->machine;
    for (size_t i = 0; i < m->host_roots_capacity; ++i) m->host_roots[i].live = 0;
    mark_host_roots(c, terms, 0, m->host_state);
    for (size_t i = 0; i < m->choice_count; ++i) {
        mark_host_roots(c, terms, 0, m->choices[i].checkpoint.host);
        if (m->choices[i].kind) mark_host_roots(c, terms, 1, m->choices[i].search.frame.premises);
    }
    for (size_t i = 0; i < m->work_count; ++i) if (c->frames[i]) mark_host_roots(c, terms, 1, m->work[i].premises);
    for (size_t i = 0; i < m->query_count; ++i) ht_collect_mark(terms, m->query[i]);
    for (size_t i = 0; i < m->work_count; ++i) if (c->frames[i]) ht_collect_mark(terms, m->work[i].goal);
    for (size_t i = 0; i < m->hyp_count; ++i) {
        if (!c->hyps[i]) continue;
        ht_collect_mark(terms, m->hyps[i].fact);
        ht_collect_mark(terms, m->hyps[i].rigid_head);
    }
    for (size_t i = 0; i < m->choice_count; ++i) {
        if (!m->choices[i].kind) continue;
        ht_collect_mark(terms, m->choices[i].search.goal);
        ht_collect_mark(terms, m->choices[i].search.head);
        ht_collect_mark(terms, m->choices[i].search.frame.goal);
    }
}

static size_t moved(const size_t *forward, size_t at)
{
    return at == NONE ? NONE : forward[at];
}

static void collect_relocate(const HTCollection *terms, void *context)
{
    Collection *c = context;
    HolV2Machine *m = c->machine;
    for (size_t i = 0; i < m->query_count; ++i) m->query[i] = ht_collect_term(terms, m->query[i]);
    for (size_t i = 0; i < m->work_count; ++i) {
        if (!c->frames[i]) continue;
        Frame frame = m->work[i];
        frame.goal = ht_collect_term(terms, frame.goal);
        frame.next = moved(c->frame_forward, frame.next);
        frame.hyps = moved(c->hyp_forward, frame.hyps);
        m->work[c->frame_forward[i]] = frame;
    }
    for (size_t i = 0; i < m->hyp_count; ++i) {
        if (!c->hyps[i]) continue;
        Hypothesis hyp = m->hyps[i];
        hyp.fact = ht_collect_term(terms, hyp.fact);
        hyp.rigid_head = hyp.rigid_head == HT_NONE ? HT_NONE : ht_collect_term(terms, hyp.rigid_head);
        hyp.next = moved(c->hyp_forward, hyp.next);
        if (hyp.undecided) hyp.undecided = c->hyp_forward[hyp.undecided - 1] + 1;
        m->hyps[c->hyp_forward[i]] = hyp;
    }
    for (size_t i = 0; i < m->choice_count; ++i) {
        Choice *choice = &m->choices[i];
        choice->checkpoint.terms.heap = ht_collect_heap(terms, choice->checkpoint.terms.heap);
        choice->checkpoint.terms.trail = ht_collect_trail(terms, choice->checkpoint.terms.trail);
        choice->checkpoint.view_trail = ht_collect_trail(terms, choice->checkpoint.view_trail);
        choice->checkpoint.work = c->frame_forward[choice->checkpoint.work];
        choice->checkpoint.hyps = c->hyp_forward[choice->checkpoint.hyps];
        if (!choice->kind) {
            choice->work_head = moved(c->frame_forward, choice->work_head);
            continue;
        }
        choice->search.goal = ht_collect_term(terms, choice->search.goal);
        choice->search.head = ht_collect_term(terms, choice->search.head);
        choice->search.local = moved(c->hyp_forward, choice->search.local);
        choice->search.local_unknown = choice->search.local_indexed ? moved(c->hyp_forward, choice->search.local_unknown) : NONE;
        choice->search.frame.goal = ht_collect_term(terms, choice->search.frame.goal);
        choice->search.frame.next = moved(c->frame_forward, choice->search.frame.next);
        choice->search.frame.hyps = moved(c->hyp_forward, choice->search.frame.hyps);
    }
    for (size_t i = 0; i < m->assignment_count; ++i) {
        Assignment *assignment = &m->assignments[i];
        if (assignment->state != ASSIGNMENT_MADE) continue;
        assignment->trail = ht_collect_trail(terms, assignment->trail);
        assignment->heap = ht_collect_heap(terms, assignment->heap);
    }
    m->view_trail = ht_collect_trail(terms, m->view_trail);
    m->assignment_trail = ht_collect_trail(terms, m->assignment_trail);
    m->assignment_heap = ht_collect_heap(terms, m->assignment_heap);
    m->work_head = moved(c->frame_forward, m->work_head);
    m->work_count = c->frame_forward[m->work_count];
    m->hyp_count = c->hyp_forward[m->hyp_count];
    /* keep_hyps retains each live row's complete .next ancestry. Stable keys
        * and that unchanged insertion sequence reproduce each surviving trie
        * path exactly; removing dead sibling versions can only reduce nodes.
        * Rebuild in place, without allocation after term relocation commits. */
    size_t previous_index_count = m->hyp_index_count;
    m->hyp_index_count = 0;
    for (size_t i = 0; i < m->hyp_count; ++i) {
        if (!index_hypothesis(m, i, 0)) return;
        if (m->hyp_index_count > previous_index_count) {
            fail(m, "V2 hypothesis collection index exceeded its old size"); return;
        }
    }
}

/* Between two goals nothing but the continuations, the choice points, the
    * disagreements and the identities known to the host can reach a term: the
    * goal executed last is dead. Compaction keeps the order of terms, frames
    * and hypotheses, so every checkpoint remains a prefix of the same state. */
static void collect(HolV2Machine *m)
{
    static const HTCollector collector = { collect_mark, collect_relocate };
    Collection c = {0};
    c.machine = m;
    c.frames = hm_calloc(m->memory, m->work_count + 1, 1);
    c.hyps = hm_calloc(m->memory, m->hyp_count + 1, 1);
    c.frame_forward = m->work_count < SIZE_MAX / sizeof(size_t) ? hm_alloc(m->memory, (m->work_count + 1) * sizeof(size_t)) : NULL;
    c.hyp_forward = m->hyp_count < SIZE_MAX / sizeof(size_t) ? hm_alloc(m->memory, (m->hyp_count + 1) * sizeof(size_t)) : NULL;
    int collected = 0;
    if (c.frames && c.hyps && c.frame_forward && c.hyp_forward) {
        keep_frames(&c, m->work_head);
        for (size_t i = 0; i < m->choice_count; ++i) {
            Choice *choice = &m->choices[i];
            if (!choice->kind) {
                keep_frames(&c, choice->work_head);
                continue;
            }
            keep_frames(&c, choice->search.frame.next);
            keep_hyps(&c, choice->search.frame.hyps);
            keep_hyps(&c, choice->search.local);
            if (choice->search.local_indexed) keep_hyps(&c, choice->search.local_unknown);
        }
        size_t frames = 0, hyps = 0;
        for (size_t i = 0; i < m->work_count; ++i) { c.frame_forward[i] = frames; frames += c.frames[i]; }
        for (size_t i = 0; i < m->hyp_count; ++i) { c.hyp_forward[i] = hyps; hyps += c.hyps[i]; }
        c.frame_forward[m->work_count] = frames;
        c.hyp_forward[m->hyp_count] = hyps;
        collected = ht_collect(m->terms, m->permanent, &collector, &c);
    }
    hm_free(c.frames);
    hm_free(c.hyps);
    hm_free(c.frame_forward);
    hm_free(c.hyp_forward);
    hm_free(c.root_seen);
    if (collected) {
        ++m->collections;
        for (size_t i = 0; i < m->host_roots_capacity; ++i) {
            HostRoots *roots = &m->host_roots[i];
            if (!roots->token || roots->token == UINT64_MAX || roots->kind >= 2 || roots->live) continue;
            erase_root(m, roots);
        }
    }
    int fault = atomic_load_explicit(&m->memory->fault, memory_order_relaxed);
    if (fault == 1) fail(m, "Native memory limit exceeded");
    else if (fault == 2) atomic_store_explicit(&m->memory->fault, 0, memory_order_relaxed);
    size_t heap = ht_heap_count(m->terms), growth = heap - m->permanent;
    if (growth < m->collect_step) growth = m->collect_step;
    size_t arena = m->work_count > SIZE_MAX - m->hyp_count ? SIZE_MAX : m->work_count + m->hyp_count;
    if (arena > growth) growth = arena;
    if (c.root_seen_count > growth) growth = c.root_seen_count;
    if (m->host_roots_capacity > growth) growth = m->host_roots_capacity;
    if (m->choice_count > growth) growth = m->choice_count;
    m->collect_at = !m->collect_step ? 0 : heap > SIZE_MAX - growth ? SIZE_MAX : heap + growth;
    m->arena_collect_at = !m->collect_step ? 0 : arena > SIZE_MAX - growth ? SIZE_MAX : arena + growth;
    m->arena_spent = 0;
}

void hol_v2_set_collection_step(HolV2Machine *m, size_t nodes)
{
    if (!m) return;
    m->collect_step = nodes;
    size_t heap = ht_heap_count(m->terms);
    m->collect_at = !nodes ? 0 : heap > SIZE_MAX - nodes ? SIZE_MAX : heap + nodes;
    size_t arena = m->work_count > SIZE_MAX - m->hyp_count ? SIZE_MAX : m->work_count + m->hyp_count;
    m->arena_collect_at = !nodes ? 0 : arena > SIZE_MAX - nodes ? SIZE_MAX : arena + nodes;
}

size_t hol_v2_heap_count(const HolV2Machine *m)
{
    return m ? ht_heap_count(m->terms) : 0;
}

size_t hol_v2_collections(const HolV2Machine *m)
{
    return m ? m->collections : 0;
}

int hol_v2_next(HolV2Machine *m)
{
    if (!m || m->error[0]) return -1;
    m->api_code = HV2_ERROR_NONE; m->api_error = NULL;
    if (m->assignment_failed && !m->event_kind) { m->assignment_failed = 0; m->action = ACTION_FAIL; }
    if (m->event_kind) return 3;
    if (m->exhausted) return 0;
    m->answer_ready = 0;
    if (m->resume_answer) {
        m->resume_answer = 0;
        m->action = ACTION_FAIL;
    }
    for (m->batch = 0; m->batch < BATCH; ++m->batch) {
        if (m->action == ACTION_FAIL) {
            if (!backtrack_step(m)) return m->error[0] ? -1 : 0;
            if (m->event_kind) return 3;
        }
        if (m->action == ACTION_SEARCH) {
            if (!search_step(m)) {
                if (m->error[0]) return -1;
                m->action = ACTION_FAIL;
            }
            if (m->event_kind) return 3;
            continue;
        }
        if (m->action == ACTION_FAIL) continue;
        if (m->assignment_dirty) {
            m->assignment_dirty = 0;
            if (m->host_state) {
                if (m->action == ACTION_NEXT && m->work_head != NONE) m->current = m->work[m->work_head];
                m->settle_action = m->action;
                event(m, HV2_EVENT_SETTLE, HT_NONE, CONTINUE_ACTION, m->action == ACTION_ANSWER);
                return 3;
            }
        }
        if (m->action == ACTION_ANSWER) {
            m->answer_ready = 1;
            m->resume_answer = 1;
            m->action = ACTION_NEXT;
            return 1;
        }
        if (m->action == ACTION_EXECUTE) {
            if (!execute_current(m)) {
                if (m->error[0]) return -1;
                m->action = ACTION_FAIL;
            }
            if (m->event_kind) return 3;
            continue;
        }
        if (m->work_head == NONE) {
            if (m->debugging && !m->end_debugged) {
                m->end_debugged = 1;
                event(m, HV2_EVENT_DEBUG, HT_NONE, CONTINUE_WORK, 1);
                return 3;
            }
            int okay = ht_retry(m->terms);
            if (okay < 0) { fail(m, ht_error(m->terms)); return -1; }
            if (!okay) { m->action = ACTION_FAIL; continue; }
            if (m->host_state) {
                event(m, HV2_EVENT_SETTLE, HT_NONE, CONTINUE_ANSWER, 1);
                return 3;
            }
            m->action = ACTION_ANSWER;
            continue;
        }
        if (ht_heap_count(m->terms) >= m->collect_at || m->arena_spent >= m->arena_collect_at || m->work_count >= m->arena_collect_at || m->hyp_count >= m->arena_collect_at - m->work_count) collect(m);
        if (m->error[0]) return -1;
        m->current = m->work[m->work_head];
        m->end_debugged = 0;
        m->work_head = m->current.next;
        m->action = ACTION_EXECUTE;
        if (m->debugging) {
            event(m, HV2_EVENT_DEBUG, m->current.goal, CONTINUE_DEBUG, 0);
            return 3;
        }
    }
    return 2;
}

int hol_v2_begin_step(HolV2Machine *m, uint64_t step_id)
{
    if (!m || m->error[0]) return -1;
    if (!step_id || step_id > INT64_MAX || m->step_id || m->exhausted) {
        m->api_code = HV2_ERROR_USAGE; m->api_error = "Invalid V2 proof-step start";
        return -1;
    }
    m->api_code = HV2_ERROR_NONE; m->api_error = NULL;
    m->step_id = step_id;
    m->step_floor = m->next_choice;
    return 1;
}

int hol_v2_end_step(HolV2Machine *m, uint64_t step_id)
{
    if (!m || m->error[0]) return -1;
    if (!step_id || m->step_id != step_id) {
        m->api_code = HV2_ERROR_USAGE; m->api_error = "V2 proof-step identity does not match the active step";
        return -1;
    }
    m->api_code = HV2_ERROR_NONE; m->api_error = NULL;
    m->step_id = 0;
    if (m->event_kind == HV2_EVENT_STEP_FAILED) {
        m->event_kind = 0;
        m->action = ACTION_FAIL;
    }
    return 1;
}

static int push_word(HolV2Machine *m, int64_t word)
{
    if (m->buffer_count == SIZE_MAX || !reserve(m, m->buffer, &m->buffer_capacity, m->buffer_count + 1, sizeof(*m->buffer))) return 0;
    m->buffer[m->buffer_count++] = word;
    return 1;
}

static int push_term(HolV2Machine *m, HTerm term)
{
    int64_t *wire = NULL;
    size_t length = 0;
    if (!((m->transient_output || m->scoped_exports) ? ht_export_transient(m->terms, term, &wire, &length) : ht_export_managed(m->terms, term, &wire, &length))) return fail(m, ht_error(m->terms));
    int success = length <= SIZE_MAX - m->buffer_count
        && reserve(m, m->buffer, &m->buffer_capacity, m->buffer_count + length, sizeof(*m->buffer));
    if (success) {
        memcpy(m->buffer + m->buffer_count, wire, length * sizeof(*wire));
        m->buffer_count += length;
    } else if (!m->error[0]) fail(m, "V2 export size overflow");
    hm_free(wire);
    return success;
}

static int copy_buffer(HolV2Machine *m, int64_t *output, size_t capacity)
{
    if (!m || m->error[0]) return -1;
    if (capacity < m->buffer_count || (m->buffer_count && !output)) { fail(m, "Invalid V2 output buffer"); return -1; }
    if (m->buffer_count) memcpy(output, m->buffer, m->buffer_count * sizeof(*output));
    return 1;
}

size_t hol_v2_failure_size(const HolV2Machine *m)
{
    return m && (m->error_code == HV2_ERROR_INVALID_GOAL || m->error_code == HV2_ERROR_INVALID_FACT) ? m->buffer_count : 0;
}

int hol_v2_failure(const HolV2Machine *m, int64_t *output, size_t capacity)
{
    size_t count = hol_v2_failure_size(m);
    if (!count || capacity < count || !output) return -1;
    memcpy(output, m->buffer, count * sizeof(*output));
    return 1;
}

size_t hol_v2_answer_size(HolV2Machine *m)
{
    if (!m || m->error[0] || !m->answer_ready) return 0;
    m->buffer_count = 0;
    if (!push_word(m, (int64_t) m->query_count)) return 0;
    for (size_t i = 0; i < m->query_count; ++i) if (!push_term(m, m->query[i])) return 0;
    return m->buffer_count;
}

int hol_v2_answer(HolV2Machine *m, int64_t *output, size_t capacity)
{
    if (!m || !m->answer_ready) return -1;
    return copy_buffer(m, output, capacity);
}

static int push_variable(HolV2Machine *m, HTerm term)
{
    ht_watch(m->terms, term);
    HTView variable = ht_view(m->terms, term);
    int typed = variable.b != HT_NONE;
    return push_word(m, typed ? HT_TYPED_VAR : HT_VAR) && push_word(m, (int64_t) variable.uid)
        && push_word(m, (int64_t) variable.scope) && push_word(m, variable.is_type)
        && push_word(m, variable.meta) && (!typed || push_term(m, variable.b));
}

size_t hol_v2_state_size(HolV2Machine *m)
{
    if (!m || m->error[0]) return 0;
    m->buffer_count = 0;
    size_t heap = ht_heap_count(m->terms), first = ht_sealed(m->terms), variables = 0;
    for (size_t i = first; i < heap; ++i) if (ht_view(m->terms, i).tag == HT_VAR) ++variables;
    if (!push_word(m, (int64_t) variables)) return 0;
    for (size_t i = first; i < heap; ++i) {
        HTView variable = ht_view(m->terms, i);
        if (variable.tag != HT_VAR) continue;
        if (!m->scoped_exports) ht_pin(m->terms, i);
        if (!push_variable(m, i) || !push_term(m, i)) return 0;
    }
    size_t pending = ht_pending_count(m->terms);
    if (!push_word(m, (int64_t) pending)) return 0;
    for (size_t i = 0; i < pending; ++i) {
        HTerm left, right;
        if (!ht_pending(m->terms, i, &left, &right) || !push_term(m, left) || !push_term(m, right)) return 0;
    }
    return m->buffer_count;
}

/* A focused debugger view has the current goal and, of its hypotheses, those
    * of the listed predicates. A hypothesis whose predicate is not known is
    * kept, so that the host decides about it. */
static int focus_keeps(const HolV2Machine *m, size_t h)
{
    HTerm head = m->hyps[h].rigid_head;
    if (head == HT_NONE) return 1;
    HTView view = ht_view(m->terms, ht_deref(m->terms, head));
    if (view.tag != HT_CONST) return 0;
    for (size_t i = 0; i < m->focus_count; ++i) if (m->focus[i] == view.symbol) return 1;
    return 0;
}

static int focused_view(const HolV2Machine *m)
{
    return m->focused && m->event_kind == HV2_EVENT_DEBUG;
}

static int selected_view_identities(HolV2Machine *m, const uint64_t *uids, size_t uid_count, int with_query, int focused, HTerm **identities, size_t *identities_count)
{
    if (!m || m->error[0]) return 0;
    HTerm *roots = NULL;
    size_t count = 0, capacity = 0;
    *identities = NULL;
    *identities_count = 0;
    int success = 1;
#define VIEW_ROOT(term) do { HTerm root = (term); if (root != HT_NONE) { if (!reserve(m, roots, &capacity, count + 1, sizeof(*roots))) success = 0; else roots[count++] = root; } } while (0)
    for (size_t i = 0; success && i < uid_count; ++i) {
        HTerm term = uids ? ht_lookup_uid(m->terms, uids[i]) : HT_NONE;
        if (term == HT_NONE) success = fail(m, "Scoped host root refers to an expired identity");
        else VIEW_ROOT(term);
    }
    if (with_query) for (size_t i = 0; success && i < m->query_count; ++i) VIEW_ROOT(m->query[i]);
    if (success && m->event_kind && m->event_kind != HV2_EVENT_STEP_FAILED) {
        VIEW_ROOT(m->current.goal);
        VIEW_ROOT(m->event_term);
        for (size_t h = m->current.hyps; success && h != NONE; h = m->hyps[h].next) if (!focused || focus_keeps(m, h)) VIEW_ROOT(m->hyps[h].fact);
    }
    for (size_t at = focused ? NONE : m->work_head; success && at != NONE; at = m->work[at].next) {
        VIEW_ROOT(m->work[at].goal);
        for (size_t h = m->work[at].hyps; success && h != NONE; h = m->hyps[h].next) VIEW_ROOT(m->hyps[h].fact);
    }
    size_t pending = ht_pending_count(m->terms);
    for (size_t i = 0; success && i < pending; ++i) {
        HTerm left, right;
        success = ht_pending(m->terms, i, &left, &right);
        if (success) { VIEW_ROOT(left); VIEW_ROOT(right); }
    }
#undef VIEW_ROOT
    if (success) success = ht_reachable_values(m->terms, roots, count, identities, identities_count);
    hm_free(roots);
    if (!success) { hm_free(*identities); *identities = NULL; return fail(m, ht_error(m->terms)); }
    return 1;
}

static size_t selected_view_state_size(HolV2Machine *m, const uint64_t *uids, size_t uid_count, int with_query, int focused)
{
    HTerm *identities = NULL;
    size_t identities_count = 0;
    if (!selected_view_identities(m, uids, uid_count, with_query, focused, &identities, &identities_count)) return 0;
    size_t pending = ht_pending_count(m->terms);
    int success;
    m->buffer_count = 0;
    success = push_word(m, 0);
    size_t variables = 0;
    for (size_t i = 0; success && i < identities_count; ++i) {
        HTerm term = identities[i];
        if (ht_view(m->terms, term).tag != HT_VAR) continue;
        if (!m->scoped_exports) ht_pin(m->terms, term);
        success = push_variable(m, term) && push_term(m, term);
        ++variables;
    }
    hm_free(identities);
    if (!success) return 0;
    m->buffer[0] = (int64_t) variables;
    if (!push_word(m, (int64_t) pending)) return 0;
    for (size_t i = 0; i < pending; ++i) {
        HTerm left, right;
        if (!ht_pending(m->terms, i, &left, &right) || !push_term(m, left) || !push_term(m, right)) return 0;
    }
    return m->buffer_count;
}

size_t hol_v2_view_state_size_with(HolV2Machine *m, const uint64_t *uids, size_t count)
{
    return selected_view_state_size(m, uids, count, 1, 0);
}

size_t hol_v2_proof_state_size_with(HolV2Machine *m, const uint64_t *uids, size_t count)
{
    return selected_view_state_size(m, uids, count, 0, m && focused_view(m));
}

/* Exact identity types need no surrounding type-binder metadata. A wire with
    * an index is conservatively left to the full occurrence-order decoder. */
static int declaration_is_closed(const int64_t *wire, size_t count)
{
    for (size_t at = 0; at < count;) {
        int64_t tag = wire[at++];
        if (tag == HT_INDEX) return 0;
        size_t words = tag == HT_VAR || tag == HT_TYPED_VAR ? 4 : tag == HT_NOMINAL || tag == HT_TYPED_NOMINAL ? 3 : tag == HT_CONST ? 2 : tag == HT_WILD ? 0 : 1;
        if (words > count - at) return 0;
        if (tag == HT_NAT) {
            if (wire[at] < 0 || (uint64_t) wire[at] > count - at - 1) return 0;
            words += (size_t) wire[at];
        } else if (tag != HT_VAR && tag != HT_TYPED_VAR && tag != HT_NOMINAL && tag != HT_TYPED_NOMINAL
            && tag != HT_CONST && tag != HT_APP && tag != HT_LAM && tag != HT_TYPED_LAM && tag != HT_WILD) return 0;
        at += words;
    }
    return 1;
}

size_t hol_v2_assignment_declarations_size_with(HolV2Machine *m, const uint64_t *uids, size_t count)
{
    if (!m || m->error[0]) return 0;
    for (size_t i = 0; i < count; ++i) {
        if (!uids || ht_lookup_uid(m->terms, uids[i]) == HT_NONE) {
            m->buffer_count = 0;
            return push_word(m, 0) ? m->buffer_count : 0;
        }
    }
    HTerm *identities = NULL;
    size_t identity_count = 0;
    if (!selected_view_identities(m, uids, count, 1, 0, &identities, &identity_count)) return 0;
    m->buffer_count = 0;
    int supported = 1, success = push_word(m, 1) && push_word(m, (int64_t) identity_count);
    for (size_t i = 0; success && supported && i < identity_count; ++i) {
        HTerm term = identities[i];
        HTView value = ht_view(m->terms, term);
        if (value.b == HT_NONE && !(value.tag == HT_VAR && value.is_type)) {
            supported = 0;
            break;
        }
        if (!m->scoped_exports) ht_pin(m->terms, term);
        size_t start = m->buffer_count;
        if (value.tag == HT_VAR) success = push_variable(m, term);
        else success = push_word(m, HT_TYPED_NOMINAL) && push_word(m, (int64_t) value.uid)
            && push_word(m, (int64_t) value.scope) && push_word(m, value.meta) && push_term(m, value.b);
        if (success) supported = declaration_is_closed(m->buffer + start, m->buffer_count - start);
    }
    hm_free(identities);
    if (!success) return 0;
    if (!supported) { m->buffer_count = 1; m->buffer[0] = 0; }
    return m->buffer_count;
}

/* A base view belongs to the branch saved with its trail watermark. Neither
    * successful forward bindings nor GC can remove a value from that base;
    * backtracking restores the earlier view instead of mutating a host map. */
size_t hol_v2_service_delta_size(HolV2Machine *m)
{
    if (!m || m->error[0]) return 0;
    if (!activate_service_deltas(m)) return 0;
    HTCheckpoint now = ht_checkpoint(m->terms);
    if (m->view_trail > now.trail) { fail(m, "Service view trail is not an ancestor"); return 0; }
    HTerm *roots = NULL, *identities = NULL;
    size_t count = 0, capacity = 0, identity_count = 0;
    int success = 1;
#define DELTA_ROOT(value) do { HTerm root = (value); if (root != HT_NONE) { if (!reserve(m, roots, &capacity, count + 1, sizeof(*roots))) success = 0; else roots[count++] = root; } } while (0)
    HostRoots *subscription = m->view_token && m->host_roots_capacity
        ? &m->host_roots[root_slot(m->host_roots, m->host_roots_capacity, 4, m->view_token)] : NULL;
    if (subscription && !subscription->token) subscription = NULL;
    for (size_t i = m->view_trail; success && i < now.trail; ++i) {
        hm_count(m->memory, HM_VISITS, 1);
        HTerm changed = ht_watched_change(m->terms, i);
        if (changed != HT_NONE && (!subscription || uid_contains(subscription->set, ht_view(m->terms, changed).uid))) DELTA_ROOT(changed);
    }
    if (success && m->event_term != HT_NONE) {
        HTerm normalized = ht_normalize(m->terms, m->event_term, HT_NF);
        if (normalized == HT_NONE) success = 0;
        else DELTA_ROOT(normalized);
    }
    size_t pending = ht_pending_count(m->terms);
    for (size_t i = 0; success && i < pending; ++i) {
        HTerm left, right;
        success = ht_pending(m->terms, i, &left, &right);
        if (success) {
            left = ht_normalize(m->terms, left, HT_NF);
            right = ht_normalize(m->terms, right, HT_NF);
            if (left == HT_NONE || right == HT_NONE) success = 0;
            else { DELTA_ROOT(left); DELTA_ROOT(right); }
        }
    }
#undef DELTA_ROOT
    if (success) success = ht_reachable_values(m->terms, roots, count, &identities, &identity_count);
    hm_free(roots);
    m->buffer_count = 0;
    m->transient_output = 1;
    if (success) success = push_word(m, (int64_t) m->view_token) && push_word(m, 0);
    size_t variables = 0;
    for (size_t i = 0; success && i < identity_count; ++i) {
        HTerm term = identities[i];
        if (ht_view(m->terms, term).tag != HT_VAR) continue;
        ht_watch(m->terms, term);
        success = push_variable(m, term) && push_term(m, term);
        ++variables;
    }
    hm_free(identities);
    if (success) {
        m->buffer[1] = (int64_t) variables;
        success = push_word(m, (int64_t) pending);
    }
    for (size_t i = 0; success && i < pending; ++i) {
        HTerm left, right;
        success = ht_pending(m->terms, i, &left, &right) && push_term(m, left) && push_term(m, right);
    }
    m->transient_output = 0;
    if (!success) { fail(m, ht_error(m->terms)); return 0; }
    return m->buffer_count;
}

size_t hol_v2_view_state_size(HolV2Machine *m)
{
    return hol_v2_view_state_size_with(m, NULL, 0);
}

int hol_v2_state(HolV2Machine *m, int64_t *output, size_t capacity)
{
    return copy_buffer(m, output, capacity);
}

size_t hol_v2_root_state_size(HolV2Machine *m, int with_query)
{
    if (!m || m->error[0]) return 0;
    m->buffer_count = 0;
    size_t variables = with_query ? m->query_count : 0;
    if (!push_word(m, (int64_t) variables)) return 0;
    for (size_t i = 0; i < variables; ++i) {
        if (!push_variable(m, m->query[i]) || !push_term(m, m->query[i])) return 0;
    }
    size_t pending = ht_pending_count(m->terms);
    if (!push_word(m, (int64_t) pending)) return 0;
    for (size_t i = 0; i < pending; ++i) {
        HTerm left, right;
        if (!ht_pending(m->terms, i, &left, &right) || !push_term(m, left) || !push_term(m, right)) return 0;
    }
    return m->buffer_count;
}

size_t hol_v2_pending_count(const HolV2Machine *m)
{
    return m && !m->error[0] ? ht_pending_count(m->terms) : 0;
}

uint64_t hol_v2_uid_frontier(const HolV2Machine *m)
{
    return m && m->terms ? ht_next_uid(m->terms) : 0;
}

int hol_v2_identity(HolV2Machine *m, uint64_t uid, int64_t *output, size_t capacity)
{
    if (!m || m->error[0]) return -1;
    HTerm term = ht_lookup_uid(m->terms, uid);
    if (term == HT_NONE) {
        fail(m, "Term wire refers to an expired identity");
        return -1;
    }
    HTView value = ht_view(m->terms, term);
    size_t count = value.tag == HT_VAR ? 5 : 4;
    if (!output || capacity < count) {
        fail(m, "Invalid V2 identity buffer");
        return -1;
    }
    output[0] = value.tag;
    output[1] = (int64_t) uid;
    output[2] = (int64_t) value.scope;
    output[3] = value.tag == HT_VAR ? value.is_type : value.meta;
    if (value.tag == HT_VAR) output[4] = value.meta;
    return (int) count;
}

size_t hol_v2_event_size(HolV2Machine *m)
{
    if (!m || m->error[0] || !m->event_kind) return 0;
    m->buffer_count = 0;
    if (!push_word(m, m->event_term == HT_NONE ? 0 : 1)) return 0;
    m->transient_output = m->service_deltas && m->event_kind != HV2_EVENT_DEBUG;
    int success = m->event_term == HT_NONE || push_term(m, m->event_term);
    m->transient_output = 0;
    return success ? m->buffer_count : 0;
}

int hol_v2_event(HolV2Machine *m, int64_t *output, size_t capacity)
{
    if (!m || !m->event_kind) return -1;
    return copy_buffer(m, output, capacity);
}

int hol_v2_event_info(const HolV2Machine *m, int64_t *output, size_t capacity)
{
    if (!m || !m->event_kind || !output || capacity < 6) return -1;
    if (m->event_kind == HV2_EVENT_STEP_FAILED) {
        memset(output, 0, 6 * sizeof(*output));
        output[0] = HV2_EVENT_STEP_FAILED;
        output[5] = m->event_aux;
        return 1;
    }
    output[0] = m->event_kind;
    output[1] = (int64_t) m->host_state;
    output[2] = (int64_t) m->current.premises;
    output[3] = (int64_t) m->current.scope;
    output[4] = (int64_t) m->current.call;
    output[5] = m->event_aux;
    return 1;
}

int hol_v2_next_event(HolV2Machine *m, int debugging, int64_t *output, size_t capacity)
{
    if (!m || !output || capacity < 7 || debugging < -1 || debugging > 1) return -1;
    if (debugging >= 0) m->debugging = debugging;
    int status = hol_v2_next(m);
    if (status == 1) output[0] = (int64_t) m->host_state;
    if (status == 3) {
        if (hol_v2_event_info(m, output, capacity) < 0) return -1;
        size_t count = hol_v2_event_size(m);
        if (!count || count > INT64_MAX) return -1;
        output[6] = (int64_t) count;
        if (count <= capacity - 7 && hol_v2_event(m, output + 7, capacity - 7) < 0) return -1;
    }
    return status;
}

uint64_t hol_v2_host_state(const HolV2Machine *m)
{
    return m ? m->host_state : 0;
}

static size_t frames_size(HolV2Machine *m, int focused)
{
    if (!m || m->error[0]) return 0;
    m->buffer_count = 0;
    if (m->event_kind == HV2_EVENT_STEP_FAILED) return push_word(m, 0) ? 1 : 0;
    size_t count = m->event_kind == HV2_EVENT_DEBUG && m->event_term != HT_NONE ? 1 : 0;
    for (size_t at = m->work_head; at != NONE; at = m->work[at].next) ++count;
    if (focused && count > 1) count = 1;
    if (!push_word(m, (int64_t) count)) return 0;
    Frame frame = m->current;
    size_t at = m->work_head;
    int current = m->event_kind == HV2_EVENT_DEBUG && m->event_term != HT_NONE;
    while (count--) {
        if (current) current = 0;
        else { frame = m->work[at]; at = frame.next; }
        size_t hyps = 0;
        for (size_t h = frame.hyps; h != NONE; h = m->hyps[h].next) if (!focused || focus_keeps(m, h)) ++hyps;
        if (!push_word(m, (int64_t) frame.scope) || !push_word(m, (int64_t) frame.call) || !push_word(m, (int64_t) hyps)) return 0;
        for (size_t h = frame.hyps; h != NONE; h = m->hyps[h].next) if ((!focused || focus_keeps(m, h)) && !push_term(m, m->hyps[h].fact)) return 0;
        if (!push_term(m, frame.goal)) return 0;
    }
    return m->buffer_count;
}

size_t hol_v2_frames_size(HolV2Machine *m)
{
    return frames_size(m, 0);
}

typedef struct {
    size_t payload, words, children[2];
    uint64_t hash;
    unsigned arity, closed_type, eligible, emitted;
} ViewNode;
typedef struct {
    ViewNode *nodes;
    size_t count, capacity, *slots, slot_capacity;
    int64_t *payload;
    size_t payload_count, payload_capacity;
} ViewGraph;
typedef struct { size_t start, words, children[2]; unsigned arity, have; } ViewParse;

static uint64_t view_hash(uint64_t hash, uint64_t word)
{
    return (hash ^ word) * UINT64_C(1099511628211);
}

static size_t view_node(HolV2Machine *m, ViewGraph *graph, const int64_t *wire, ViewParse frame)
{
    uint64_t hash = UINT64_C(14695981039346656037);
    for (size_t i = 0; i < frame.words; ++i) hash = view_hash(hash, (uint64_t) wire[frame.start + i]);
    for (unsigned i = 0; i < frame.arity; ++i) hash = view_hash(hash, (uint64_t) frame.children[i]);
    if (!graph->slot_capacity || graph->count >= graph->slot_capacity / 2) {
        size_t capacity = graph->slot_capacity ? graph->slot_capacity * 2 : 64;
        if (capacity < graph->slot_capacity) { fail(m, "V2 view dictionary size overflow"); return NONE; }
        size_t *slots = hm_calloc(m->memory, capacity, sizeof(*slots));
        if (!slots) { fail(m, "V2 view dictionary allocation failed"); return NONE; }
        for (size_t i = 0; i < graph->count; ++i) {
            size_t at = (size_t) graph->nodes[i].hash & (capacity - 1);
            while (slots[at]) at = (at + 1) & (capacity - 1);
            slots[at] = i + 1;
        }
        hm_free(graph->slots);
        graph->slots = slots;
        graph->slot_capacity = capacity;
    }
    size_t slot = (size_t) hash & (graph->slot_capacity - 1);
    while (graph->slots[slot]) {
        size_t id = graph->slots[slot] - 1;
        ViewNode node = graph->nodes[id];
        if (node.hash == hash && node.words == frame.words && node.arity == frame.arity
            && !memcmp(graph->payload + node.payload, wire + frame.start, frame.words * sizeof(*wire))
            && (!frame.arity || node.children[0] == frame.children[0])
            && (frame.arity < 2 || node.children[1] == frame.children[1])) return id;
        slot = (slot + 1) & (graph->slot_capacity - 1);
    }
    if (graph->count >= INT64_MAX || frame.words > SIZE_MAX - graph->payload_count) { fail(m, "V2 view dictionary size overflow"); return NONE; }
    if (!reserve(m, graph->nodes, &graph->capacity, graph->count + 1, sizeof(*graph->nodes))
        || !reserve(m, graph->payload, &graph->payload_capacity, graph->payload_count + frame.words, sizeof(*graph->payload))) return NONE;
    int64_t tag = wire[frame.start];
    unsigned eligible = tag != HT_VAR && tag != HT_NOMINAL;
    if (tag == HT_CONST) {
        int64_t symbol = wire[frame.start + 1];
        eligible = symbol >= 0 && (uint64_t) symbol < m->symbol_count && ROLE(m, (size_t) symbol) != HV2_TY_PI;
    }
    for (unsigned i = 0; i < frame.arity; ++i) eligible &= graph->nodes[frame.children[i]].eligible;
    if (tag == HT_TYPED_VAR || tag == HT_TYPED_NOMINAL || tag == HT_TYPED_LAM) eligible &= graph->nodes[frame.children[0]].closed_type;
    unsigned closed = tag == HT_CONST || (tag == HT_APP && graph->nodes[frame.children[0]].closed_type && graph->nodes[frame.children[1]].closed_type);
    size_t id = graph->count++;
    graph->nodes[id] = (ViewNode) { graph->payload_count, frame.words, { frame.children[0], frame.children[1] }, hash, frame.arity, closed, eligible, 0 };
    memcpy(graph->payload + graph->payload_count, wire + frame.start, frame.words * sizeof(*wire));
    graph->payload_count += frame.words;
    graph->slots[slot] = id + 1;
    return id;
}

static size_t parse_view_term(HolV2Machine *m, ViewGraph *graph, const int64_t *wire, size_t length)
{
    ViewParse *stack = NULL;
    size_t count = 0, capacity = 0, at = 0, root = NONE;
    while (at < length && !m->error[0]) {
        size_t start = at;
        int64_t tag = wire[at++];
        size_t words = tag == HT_VAR || tag == HT_TYPED_VAR ? 4 : tag == HT_NOMINAL || tag == HT_TYPED_NOMINAL ? 3 : tag == HT_CONST ? 2 : tag == HT_WILD ? 0 : 1;
        if (words > length - at || tag < HT_VAR || tag > HT_TYPED_NOMINAL) { fail(m, "Invalid V2 view term wire"); break; }
        if (tag == HT_NAT) {
            if (wire[at] < 0 || (uint64_t) wire[at] > length - at - 1) { fail(m, "Invalid V2 view natural"); break; }
            words += (size_t) wire[at];
        }
        at += words;
        unsigned arity = tag == HT_APP || tag == HT_TYPED_LAM ? 2 : tag == HT_LAM || tag == HT_TYPED_VAR || tag == HT_TYPED_NOMINAL ? 1 : 0;
        ViewParse frame = { start, words + 1, { NONE, NONE }, arity, 0 };
        if (arity) {
            if (!reserve(m, stack, &capacity, count + 1, sizeof(*stack))) break;
            stack[count++] = frame;
            continue;
        }
        size_t node = view_node(m, graph, wire, frame);
        while (node != NONE && count) {
            ViewParse *parent = &stack[count - 1];
            parent->children[parent->have++] = node;
            if (parent->have < parent->arity) break;
            frame = *parent;
            --count;
            node = view_node(m, graph, wire, frame);
        }
        if (node == NONE) break;
        if (!count) { root = node; break; }
    }
    hm_free(stack);
    if (!m->error[0] && (root == NONE || at != length)) fail(m, "Incomplete V2 view term wire");
    return m->error[0] ? NONE : root;
}

static int view_room_part(size_t *room, size_t base, size_t extra, size_t width)
{
    if (extra > SIZE_MAX - base || base + extra > *room / width) return 0;
    *room -= (base + extra) * width;
    return 1;
}

/* Compression is optional. Reserve a conservative bound before touching its
    * graph: geometric vectors, simultaneous hash tables, traversal stacks,
    * payload and output. An insufficient cap takes the ordinary exporter;
    * actual allocation failures remain errors, never cleared for fallback. */
static int view_graph_room(HolV2Machine *m, const ViewGraph *graph, size_t length)
{
    size_t limit = atomic_load_explicit(&m->memory->limit, memory_order_relaxed);
    if (!limit) return 1;
    size_t used = atomic_load_explicit(&m->memory->bytes, memory_order_relaxed);
    if (used >= limit || length > (SIZE_MAX - 64) / 3) return 0;
    size_t room = limit - used;
    return view_room_part(&room, graph->count, length + 64, 2 * sizeof(ViewNode) + 6 * sizeof(size_t))
        && view_room_part(&room, 0, length + 64, 2 * sizeof(ViewParse) + 2 * sizeof(size_t))
        && view_room_part(&room, graph->payload_count, length + 64, 2 * sizeof(int64_t))
        && view_room_part(&room, m->buffer_count, 3 * length + 64, 2 * sizeof(int64_t))
        && view_room_part(&room, 0, 16, sizeof(HMemoryHeader));
}

static int push_view_term(HolV2Machine *m, ViewGraph *graph, HTerm term, int *supported)
{
    int64_t *wire = NULL;
    size_t length = 0;
    if (!((m->transient_output || m->scoped_exports) ? ht_export_transient(m->terms, term, &wire, &length) : ht_export_managed(m->terms, term, &wire, &length))) return fail(m, ht_error(m->terms));
    if (!view_graph_room(m, graph, length)) { hm_free(wire); *supported = 0; return 1; }
    size_t root = parse_view_term(m, graph, wire, length);
    hm_free(wire);
    if (root == NONE) return 0;
    if (!graph->nodes[root].eligible) { *supported = 0; return 1; }
    size_t *stack = NULL, count = 0, capacity = 0;
    int success = reserve(m, stack, &capacity, 1, sizeof(*stack));
    if (success) stack[count++] = root;
    while (success && count) {
        size_t id = stack[--count];
        ViewNode node = graph->nodes[id];
        success = push_word(m, node.emitted ? 12 : 11) && push_word(m, (int64_t) id);
        if (!success || node.emitted) continue;
        graph->nodes[id].emitted = 1;
        for (size_t i = 0; success && i < node.words; ++i) success = push_word(m, graph->payload[node.payload + i]);
        if (success && node.arity) {
            success = reserve(m, stack, &capacity, count + node.arity, sizeof(*stack));
            for (unsigned i = node.arity; success && i; --i) stack[count++] = node.children[i - 1];
        }
    }
    hm_free(stack);
    return success;
}

static size_t compact_frames_size(HolV2Machine *m, int focused)
{
    if (!m || m->error[0]) return 0;
    if (m->event_kind == HV2_EVENT_STEP_FAILED) return hol_v2_frames_size(m);
    if (m->hyp_count > INT64_MAX) { fail(m, "V2 hypothesis dictionary size overflow"); return 0; }
    unsigned char *seen = m->hyp_count ? hm_calloc(m->memory, m->hyp_count, sizeof(*seen)) : NULL;
    if (m->hyp_count && !seen) { fail(m, "V2 hypothesis dictionary allocation failed"); return 0; }
    size_t count = m->event_kind == HV2_EVENT_DEBUG && m->event_term != HT_NONE ? 1 : 0;
    for (size_t at = m->work_head; at != NONE; at = m->work[at].next) ++count;
    if (focused && count > 1) count = 1;
    size_t left = count;
    m->buffer_count = 0;
    ViewGraph graph = { 0 };
    int success = push_word(m, -2) && push_word(m, (int64_t) count), supported = 1;
    Frame frame = m->current;
    size_t at = m->work_head;
    int current = m->event_kind == HV2_EVENT_DEBUG && m->event_term != HT_NONE;
    while (success && supported && left--) {
        if (current) current = 0;
        else { frame = m->work[at]; at = frame.next; }
        success = push_word(m, (int64_t) frame.scope) && push_word(m, (int64_t) frame.call);
        size_t h = frame.hyps;
        while (success && supported && h != NONE && !seen[h]) {
            seen[h] = 1;
            if (!focused || focus_keeps(m, h)) {
                success = push_word(m, 1) && push_word(m, (int64_t) h);
                if (success) success = push_view_term(m, &graph, m->hyps[h].fact, &supported);
            }
            h = m->hyps[h].next;
        }
        if (success && supported) success = h == NONE ? push_word(m, 0) : push_word(m, 2) && push_word(m, (int64_t) h);
        if (success && supported) success = push_view_term(m, &graph, frame.goal, &supported);
    }
    hm_free(seen);
    hm_free(graph.nodes);
    hm_free(graph.slots);
    hm_free(graph.payload);
    if (!success) return 0;
    return supported ? m->buffer_count : frames_size(m, focused);
}

size_t hol_v2_compact_frames_size(HolV2Machine *m)
{
    return compact_frames_size(m, 0);
}

size_t hol_v2_proof_frames_size(HolV2Machine *m)
{
    return compact_frames_size(m, m && focused_view(m));
}

int hol_v2_frames(HolV2Machine *m, int64_t *output, size_t capacity)
{
    return copy_buffer(m, output, capacity);
}

static int skip_wire(const int64_t *wire, size_t length, size_t *offset);

static int term_declarations(HolV2Machine *m, HTerm term, size_t *count)
{
    int64_t *wire = NULL;
    size_t length = 0;
    if (!((m->transient_output || m->scoped_exports) ? ht_export_transient(m->terms, term, &wire, &length) : ht_export_managed(m->terms, term, &wire, &length))) return fail(m, ht_error(m->terms));
    int success = 1;
    for (size_t at = 0; success && at < length;) {
        size_t start = at++;
        int64_t tag = wire[start];
        size_t payload = tag == HT_VAR || tag == HT_TYPED_VAR ? 4 : tag == HT_NOMINAL || tag == HT_TYPED_NOMINAL ? 3 : tag == HT_CONST ? 2 : tag == HT_WILD ? 0 : 1;
        if (payload > length - at) { success = fail(m, "Truncated V2 declaration source"); break; }
        if (tag == HT_VAR || tag == HT_NOMINAL || tag == HT_TYPED_VAR || tag == HT_TYPED_NOMINAL) {
            size_t end = at + payload;
            if ((tag == HT_TYPED_VAR || tag == HT_TYPED_NOMINAL) && !skip_wire(wire, length, &end)) {
                success = fail(m, "Invalid V2 declaration type");
                break;
            }
            ++*count;
            for (size_t i = start; success && i < end; ++i) success = push_word(m, wire[i]);
            payload = end - at;
        } else if (tag == HT_NAT) {
            if (wire[at] < 0 || (uint64_t) wire[at] > length - at - 1) { success = fail(m, "Invalid V2 declaration natural"); break; }
            payload += (size_t) wire[at];
        } else if (tag != HT_CONST && tag != HT_APP && tag != HT_INDEX && tag != HT_LAM && tag != HT_TYPED_LAM && tag != HT_WILD) {
            success = fail(m, "Invalid V2 declaration source tag");
            break;
        }
        at += payload;
    }
    hm_free(wire);
    return success;
}

size_t hol_v2_declarations_size(HolV2Machine *m)
{
    if (!m || m->error[0]) return 0;
    m->buffer_count = 0;
    if (m->event_kind == HV2_EVENT_STEP_FAILED) return push_word(m, 0) ? 1 : 0;
    size_t count = 0;
    int success = push_word(m, 0);
    for (size_t at = m->work_head; success && at != NONE; at = m->work[at].next) {
        Frame frame = m->work[at];
        for (size_t h = frame.hyps; success && h != NONE; h = m->hyps[h].next) {
            success = term_declarations(m, m->hyps[h].fact, &count);
        }
        if (success) success = term_declarations(m, frame.goal, &count);
    }
    if (!success) return 0;
    m->buffer[0] = (int64_t) count;
    return m->buffer_count;
}

int hol_v2_declarations(HolV2Machine *m, int64_t *output, size_t capacity)
{
    return copy_buffer(m, output, capacity);
}

size_t hol_v2_hypotheses_size(HolV2Machine *m)
{
    if (!m || m->error[0]) return 0;
    m->buffer_count = 0;
    if (m->event_kind == HV2_EVENT_STEP_FAILED) return push_word(m, 0) && push_word(m, 0) ? 2 : 0;
    size_t hyps = 0;
    for (size_t h = m->current.hyps; h != NONE; h = m->hyps[h].next) ++hyps;
    if (!push_word(m, (int64_t) m->current.scope) || !push_word(m, (int64_t) hyps)) return 0;
    for (size_t h = m->current.hyps; h != NONE; h = m->hyps[h].next) if (!push_term(m, m->hyps[h].fact)) return 0;
    return m->buffer_count;
}

int hol_v2_hypotheses(HolV2Machine *m, int64_t *output, size_t capacity)
{
    return copy_buffer(m, output, capacity);
}

int hol_v2_resume(HolV2Machine *m, int result, uint64_t host_state, uint64_t premises, const int64_t *bindings, size_t length)
{
    if (!m || m->error[0] || !m->event_kind) return -1;
    if (m->event_kind == HV2_EVENT_STEP_FAILED) {
        m->api_code = HV2_ERROR_USAGE; m->api_error = "V2 proof-step failure requires end_step or snapshot restore";
        return -1;
    }
    if (result < 0 || result > 4 || host_state > INT64_MAX || premises > INT64_MAX || !bindings || !length || bindings[0] < 0) {
        fail(m, "Invalid V2 host response");
        return -1;
    }
    int continuation = m->event_continuation;
    m->event_kind = 0;
    if (m->assignment_failed) { m->assignment_failed = 0; m->action = ACTION_FAIL; return 1; }
    if (!result) { m->action = ACTION_FAIL; return 1; }
    size_t at = 1;
    uint64_t count = (uint64_t) bindings[0];
    for (uint64_t i = 0; i < count; ++i) {
        HTerm left = m->service_deltas ? ht_import_transient(m->terms, bindings, length, &at) : ht_import(m->terms, bindings, length, &at);
        HTerm right = m->service_deltas ? ht_import_transient(m->terms, bindings, length, &at) : ht_import(m->terms, bindings, length, &at);
        if (!term_ok(m, left) || !term_ok(m, right)) return -1;
        int unified = ht_unify(m->terms, left, right);
        if (unified < 0) { fail(m, ht_error(m->terms)); return -1; }
        if (!unified) { m->action = ACTION_FAIL; return 1; }
    }
    if (at != length) { fail(m, "Trailing V2 host binding words"); return -1; }
    if (!change_token(m, 3, &m->host_state, host_state)) return -1;
    m->action = ACTION_NEXT;
    int success = 1;
    switch (continuation) {
        case CONTINUE_IMPLY:
            success = enter_implication(m, premises);
            break;
        case CONTINUE_EQUALITY:
            success = begin_search(m, result, NULL);
            break;
        case CONTINUE_DEBUG:
            m->action = ACTION_EXECUTE;
            break;
        case CONTINUE_ANSWER:
            m->action = ACTION_ANSWER;
            break;
        case CONTINUE_ACTION:
            m->action = m->settle_action;
            break;
        default:
            break;
    }
    if (!success) {
        if (m->error[0]) return -1;
        m->action = ACTION_FAIL;
    }
    return 1;
}

int hol_v2_resume_with_view(HolV2Machine *m, int result, uint64_t host, uint64_t premises,
    uint64_t view, const int64_t *bindings, size_t length)
{
    if (!m || m->error[0] || !m->event_kind) return -1;
    if (m->event_kind == HV2_EVENT_STEP_FAILED) return api_failure(m, HV2_ERROR_USAGE, "V2 proof-step failure requires end_step or snapshot restore");
    if (!view || view > INT64_MAX || view <= m->last_view_token) return api_failure(m, HV2_ERROR_USAGE, "Service view tokens must increase monotonically");
    if (!activate_service_deltas(m) || !change_token(m, 2, &m->view_token, view)) return -1;
    m->last_view_token = view;
    m->view_trail = ht_checkpoint(m->terms).trail;
    return hol_v2_resume(m, result, host, premises, bindings, length);
}

/* The staged sets own their roots before resume can retire a parent token.
    * UID existence is checked after reply import: a host may reserve and then
    * materialize an identity in those bindings. No collection or host callback
    * occurs between import and publication. Resource failure interrupts the
    * operation and requires restoration, like failure while importing terms. */
int hol_v2_resume_with_root_deltas(HolV2Machine *m, int result, uint64_t host, uint64_t premises,
    uint64_t view, const int64_t *bindings, size_t length, const uint64_t *wire, size_t count)
{
    if (!m || m->error[0] || !m->event_kind) return -1;
    if (!wire || !count || wire[0] > 3) return api_failure(m, HV2_ERROR_USAGE, "Invalid host root delta");
    HostRoots staged[3] = {{0}};
    const uint64_t *added[3] = { NULL, NULL, NULL };
    size_t added_count[3] = { 0, 0, 0 }, at = 1, entries = (size_t) wire[0];
    int status = -1;
    for (size_t i = 0; i < entries; ++i) {
        if (count - at < 4) goto malformed;
        uint64_t kind = wire[at++], token = wire[at++], parent = wire[at++], add = wire[at++];
        if ((kind > 1 && kind != 4) || !token || token > INT64_MAX
            || token != (kind == 4 ? view : kind == 1 ? premises : host) || add > count - at) goto malformed;
        for (size_t j = 0; j < i; ++j) if (staged[j].kind == (int) kind) goto malformed;
        HostRoots *old = NULL;
        if (parent) {
            if (!m->host_roots_capacity) goto missing_parent;
            old = &m->host_roots[root_slot(m->host_roots, m->host_roots_capacity, (int) kind, parent)];
            if (!old->token) goto missing_parent;
        }
        staged[i] = (HostRoots) { token, old ? old->set : NULL, old ? old->count : 0, (int) kind, 0 };
        index_retain(staged[i].set);
        added[i] = wire + at;
        added_count[i] = (size_t) add;
        at += (size_t) add;
        if (at == count) goto malformed;
        uint64_t remove = wire[at++];
        if (remove > count - at) goto malformed;
        for (size_t j = 0; j < (size_t) remove; ++j) {
            int changed = 0;
            BucketIndex *next = uid_remove(m, staged[i].set, wire[at++], &changed);
            index_release(staged[i].set);
            staged[i].set = next;
            if (m->error[0]) goto finish;
            staged[i].count -= (size_t) changed;
        }
        for (size_t j = 0; j < added_count[i]; ++j) {
            if (added[i][j] >= INT64_MAX) goto malformed;
            int changed = 0;
            BucketIndex *next = uid_insert(m, staged[i].set, added[i][j], &changed);
            index_release(staged[i].set);
            staged[i].set = next;
            if (m->error[0]) goto finish;
            staged[i].count += (size_t) changed;
        }
        if (m->host_roots_capacity) {
            old = &m->host_roots[root_slot(m->host_roots, m->host_roots_capacity, (int) kind, token)];
            if (old->token && (old->count != staged[i].count || !uid_equal(old->set, staged[i].set))) {
                api_failure(m, HV2_ERROR_USAGE, "A host root token is immutable");
                goto finish;
            }
        }
    }
    if (at != count) goto malformed;
    status = hol_v2_resume_with_view(m, result, host, premises, view, bindings, length);
    if (status < 0 || m->action == ACTION_FAIL) goto finish;
    for (size_t i = 0; i < entries; ++i) {
        for (size_t j = 0; j < added_count[i]; ++j) {
            HTerm term = ht_lookup_uid(m->terms, added[i][j]);
            if (term == HT_NONE) { fail(m, "Host root delta names an expired identity"); status = -1; goto finish; }
            ht_watch(m->terms, term);
        }
    }
    for (size_t i = 0; i < entries; ++i) {
        HostRoots *entry = insert_root(m, staged[i].kind, staged[i].token);
        if (!entry) { status = -1; goto finish; }
        index_release(entry->set);
        *entry = staged[i];
        staged[i].set = NULL;
    }
    goto finish;
malformed:
    api_failure(m, HV2_ERROR_USAGE, "Invalid host root delta");
    goto finish;
missing_parent:
    api_failure(m, HV2_ERROR_USAGE, "Host root delta parent is no longer live");
finish:
    for (size_t i = 0; i < 3; ++i) index_release(staged[i].set);
    return status;
}

void hol_v2_set_debugging(HolV2Machine *m, int enabled)
{
    if (m) m->debugging = enabled != 0;
}

int hol_v2_ensure_symbol(HolV2Machine *m, size_t symbol, int operation)
{
    if (!m || m->error[0]) return -1;
    if (operation < HV2_ORDINARY || operation > HV2_TYPE || symbol >= INT64_MAX || symbol >= SIZE_MAX / sizeof(int64_t)) return fail(m, "Invalid V2 dynamic symbol") ? 1 : -1;
    if (symbol < m->symbol_count) {
        if (ROLE(m, symbol) != operation) { fail(m, "V2 dynamic symbol role conflict"); return -1; }
        return set_symbol_role(m, symbol, operation) ? 1 : -1;
    }
    if (operation == HV2_SUCCESSOR && m->truth != HT_NONE) return fail(m, "A V2 fragment declares another successor symbol") ? 1 : -1;
    return append_symbol_role(m, symbol, operation) ? 1 : -1;
}

uint64_t hol_v2_reserve_uid(HolV2Machine *m)
{
    if (!m || m->error[0]) return UINT64_MAX;
    uint64_t uid = ht_next_uid(m->terms);
    if (uid >= INT64_MAX || !ht_advance_uid(m->terms, uid + 1)) { fail(m, "V2 variable identity exhausted"); return UINT64_MAX; }
    return uid;
}

static void release_fields(HolV2Machine *m)
{
    ht_destroy(m->terms);
    index_release(m->bucket_index);
    hm_lease_release(m->index_lease);
    clear_host_roots(m);
    hm_free(m->retired_tokens);
    release_version(m->version);
    hm_lease_release(m->version_lease);
    for (size_t i = 0; i < TABLE_COUNT; ++i) hm_lease_release(m->table_leases[i]);
    for (size_t i = 0; i < TABLE_COUNT; ++i) hv_destroy(&m->program[i]);
    hm_free(m->query);
    hm_free(m->focus);
    hm_free(m->work);
    hm_free(m->hyps);
    hm_free(m->hyp_index);
    hm_free(m->choices);
    hm_free(m->buffer);
    for (size_t i = 0; i < m->assignment_count; ++i) hm_free(m->assignments[i].wire);
    hm_free(m->assignments);
}

void hol_v2_destroy(HolV2Machine *m)
{
    if (m) { HMemory *memory = m->memory; release_fields(m); hm_free(m); hm_release(memory); }
}

const char *hol_v2_error(const HolV2Machine *m)
{
    return m ? (m->error[0] ? m->error : m->api_error ? m->api_error : "") : "V2 allocation failed";
}

static HolV2Machine *clone_in(const HolV2Machine *source, HMemory *memory)
{
    if (!source || source->error[0]) return NULL;
    HolV2Machine *copy = hm_calloc(memory, 1, sizeof(*copy));
    if (!copy) return NULL;
    *copy = *source;
    copy->focus = NULL;
    if (source->api_error == source->api_message) copy->api_error = copy->api_message;
    copy->memory = memory;
    hm_retain(memory);
    memset(copy->table_leases, 0, sizeof(copy->table_leases));
    index_retain(copy->bucket_index);
    copy->index_lease = NULL;
    if (!source->legacy_copy) {
        if (memory == source->memory) { copy->index_lease = source->index_lease; hm_lease_retain(copy->index_lease); }
        else if (copy->bucket_index) copy->index_lease = hm_lease(memory, copy->bucket_index->bytes);
    }
    retain_version(copy->version);
    copy->version_lease = NULL;
    if (memory == source->memory) {
        copy->version_lease = source->version_lease;
        hm_lease_retain(copy->version_lease);
    } else if (copy->version) copy->version_lease = hm_lease(memory, copy->version->bytes);
    copy->assignment_count = 0;
    copy->assignment_capacity = source->assignment_count;
    copy->assignments = source->assignment_count ? hm_calloc(memory, source->assignment_count, sizeof(*source->assignments)) : NULL;
    copy->host_roots = source->host_roots_capacity ? hm_calloc(memory, source->host_roots_capacity, sizeof(*copy->host_roots)) : NULL;
    if (!copy->host_roots) copy->host_roots_capacity = 0;
    int roots_copied = !source->host_roots_capacity || copy->host_roots;
    for (size_t i = 0; roots_copied && i < source->host_roots_capacity; ++i) {
        copy->host_roots[i] = source->host_roots[i];
        if (memory == source->memory) index_retain(copy->host_roots[i].set);
        else {
            copy->host_roots[i].set = copy_tree(copy, source->host_roots[i].set, 0);
            if (source->host_roots[i].set && !copy->host_roots[i].set) roots_copied = 0;
        }
    }
    copy->terms = ht_clone_in(source->terms, memory, source->legacy_copy);
    int leased = (memory == source->memory || !copy->version || copy->version_lease)
        && (source->legacy_copy || memory == source->memory || !copy->bucket_index || copy->index_lease);
    if (source->legacy_copy && source->bucket_index) {
        BucketIndex *index = copy_tree(copy, source->bucket_index, 1);
        index_release(copy->bucket_index);
        copy->bucket_index = index;
        if (!index) leased = 0;
    }
    for (size_t i = 0; i < TABLE_COUNT; ++i) {
        if (source->legacy_copy) {
            hv_init(&copy->program[i], memory, source->program[i].width, source->program[i].copy, NULL);
            for (size_t j = 0; j < source->program[i].count; ++j) {
                if (!hv_append(&copy->program[i], hv_get(&source->program[i], j))) { leased = 0; break; }
            }
        } else {
            hv_clone(&copy->program[i], &source->program[i], memory);
            if (memory == source->memory) {
                copy->table_leases[i] = source->table_leases[i];
                hm_lease_retain(copy->table_leases[i]);
            } else if (source->program[i].root) {
                copy->table_leases[i] = hm_lease(memory, hv_bytes(&source->program[i]));
                if (!copy->table_leases[i]) leased = 0;
            }
        }
    }
    copy->retired_tokens = copy_array(memory, source->retired_tokens, source->retired_count, sizeof(*source->retired_tokens));
    copy->retired_capacity = source->retired_count;
    copy->query = copy_array(memory, source->query, source->query_count, sizeof(*source->query));
    copy->work = copy_array(memory, source->work, source->work_count, sizeof(*source->work));
    copy->hyps = copy_array(memory, source->hyps, source->hyp_count, sizeof(*source->hyps));
    copy->hyp_index = copy_array(memory, source->hyp_index, source->hyp_index_count, sizeof(*source->hyp_index));
    copy->choices = copy_array(memory, source->choices, source->choice_count, sizeof(*source->choices));
    copy->buffer = copy_array(memory, source->buffer, source->buffer_count, sizeof(*source->buffer));
    copy->focus = copy_array(memory, source->focus, source->focus_count, sizeof(*source->focus));
    copy->work_capacity = copy->work_count;
    copy->hyp_capacity = copy->hyp_count;
    copy->hyp_index_capacity = copy->hyp_index_count;
    copy->choice_capacity = copy->choice_count;
    copy->buffer_capacity = copy->buffer_count;
    if (!leased || !roots_copied || !copy->terms || (source->assignment_count && !copy->assignments)
        || (copy->query_count && !copy->query) || (copy->work_count && !copy->work)
        || (copy->hyp_count && !copy->hyps) || (copy->hyp_index_count && !copy->hyp_index) || (copy->choice_count && !copy->choices)
        || (copy->buffer_count && !copy->buffer) || (copy->focus_count && !copy->focus) || (copy->retired_count && !copy->retired_tokens)) {
        hol_v2_destroy(copy);
        return NULL;
    }
    for (size_t i = 0; i < source->assignment_count; ++i) {
        Assignment original = source->assignments[i];
        int64_t *wire = copy_array(memory, original.wire, original.length, sizeof(*wire));
        if (!wire) { hol_v2_destroy(copy); return NULL; }
        copy->assignments[copy->assignment_count] = original;
        copy->assignments[copy->assignment_count++].wire = wire;
    }
    return copy;
}

HolV2Machine *hol_v2_clone(const HolV2Machine *source)
{
    return source ? clone_in(source, source->memory) : NULL;
}

HolV2Machine *hol_v2_snapshot(HolV2Machine *source)
{
    if (!source || source->error[0]) return NULL;
    source->api_code = HV2_ERROR_NONE; source->api_error = NULL;
    atomic_store_explicit(&source->memory->fault, 0, memory_order_relaxed);
    HolV2Machine *copy = hol_v2_clone(source);
    if (!copy) {
        int fault = atomic_load_explicit(&source->memory->fault, memory_order_relaxed);
        api_failure(source, fault == 1 ? HV2_ERROR_MEMORY : HV2_ERROR_ALLOCATION, fault == 1 ? "Native memory limit exceeded" : "V2 snapshot allocation failed");
    }
    return copy;
}

HolV2Machine *hol_v2_fork(const HolV2Machine *source)
{
    if (!source || source->error[0]) return NULL;
    HMemory *memory = hm_create();
    if (!memory) return NULL;
    atomic_store_explicit(&memory->limit, hol_v2_memory_limit(source), memory_order_relaxed);
    HolV2Machine *copy = clone_in(source, memory);
    hm_release(memory);
    if (copy && !leave_run(copy)) { hol_v2_destroy(copy); copy = NULL; }
    if (copy) copy->engine_origin = copy->origin;
    return copy;
}

int hol_v2_restore(HolV2Machine *m, const HolV2Machine *snapshot)
{
    if (!m || !snapshot) return -1;
    if (m->origin != snapshot->origin || snapshot->error[0]) {
        m->api_code = HV2_ERROR_USAGE; m->api_error = "Snapshot belongs to a different V2 runtime or contains an error";
        return -1;
    }
    m->api_code = HV2_ERROR_NONE; m->api_error = NULL;
    HolV2Machine *restored = hol_v2_clone(snapshot);
    if (!restored) { fail(m, "V2 snapshot allocation failed"); return -1; }
    if (!ht_preserve_identity_history(restored->terms, m->terms)) {
        hol_v2_destroy(restored);
        fail(m, "V2 snapshot identity preservation failed");
        return -1;
    }
    if (m->last_view_token > restored->last_view_token) restored->last_view_token = m->last_view_token;
    if (m->next_call > restored->next_call) restored->next_call = m->next_call;
    if (m->next_choice > restored->next_choice) restored->next_choice = m->next_choice;
    for (size_t i = restored->symbol_count; i < m->symbol_count; ++i) {
        if (hol_v2_ensure_symbol(restored, i, (int) ROLE(m, i)) < 0) {
            hol_v2_destroy(restored);
            fail(m, "V2 snapshot symbol preservation failed");
            return -1;
        }
    }
    if (!ht_set_work_limit(restored->terms, ht_work_limit(m->terms))) {
        hol_v2_destroy(restored);
        fail(m, "V2 snapshot work-limit preservation failed");
        return -1;
    }
    int debugging = m->debugging;
    release_fields(m);
    *m = *restored;
    if (restored->api_error == restored->api_message) m->api_error = m->api_message;
    m->debugging = debugging;
    hm_free(restored);
    hm_release(m->memory);
    atomic_store_explicit(&m->memory->fault, 0, memory_order_relaxed);
    return 1;
}

int hol_v2_restore_consuming(HolV2Machine *m, HolV2Machine *snapshot)
{
    if (!m || !snapshot) return -1;
    if (m == snapshot || m->origin != snapshot->origin || m->memory != snapshot->memory
        || snapshot->error[0] || snapshot->symbol_count > m->symbol_count) {
        return api_failure(m, HV2_ERROR_USAGE, "Snapshot belongs to a different V2 runtime or has been consumed");
    }
    atomic_store_explicit(&m->memory->fault, 0, memory_order_relaxed);
    if (!ht_consume_history(snapshot->terms, m->terms)) {
        int fault = atomic_load_explicit(&m->memory->fault, memory_order_relaxed);
        return api_failure(m, fault == 1 ? HV2_ERROR_MEMORY : fault == 2 ? HV2_ERROR_ALLOCATION : HV2_ERROR_INTERNAL, "V2 consuming restore metadata preservation failed");
    }
    /* No fallible operation follows the metadata transfer. The immutable role
        * vector carries appended dynamic symbols without copying its rows. */
    hv_destroy(&snapshot->program[TABLE_ROLES]);
    snapshot->program[TABLE_ROLES] = m->program[TABLE_ROLES];
    memset(&m->program[TABLE_ROLES], 0, sizeof(m->program[TABLE_ROLES]));
    hm_lease_release(snapshot->table_leases[TABLE_ROLES]);
    snapshot->table_leases[TABLE_ROLES] = m->table_leases[TABLE_ROLES];
    m->table_leases[TABLE_ROLES] = NULL;
    snapshot->symbol_count = m->symbol_count;
    if (m->last_view_token > snapshot->last_view_token) snapshot->last_view_token = m->last_view_token;
    if (m->next_call > snapshot->next_call) snapshot->next_call = m->next_call;
    if (m->next_choice > snapshot->next_choice) snapshot->next_choice = m->next_choice;
    snapshot->debugging = m->debugging;
    release_fields(m);
    *m = *snapshot;
    if (snapshot->api_error == snapshot->api_message) m->api_error = m->api_message;
    m->api_code = HV2_ERROR_NONE; m->api_error = NULL;
    memset(snapshot, 0, sizeof(*snapshot));
    snapshot->memory = m->memory;
    snapshot->error_code = HV2_ERROR_USAGE;
    memcpy(snapshot->error, "Snapshot has been consumed", sizeof("Snapshot has been consumed"));
    atomic_store_explicit(&m->memory->fault, 0, memory_order_relaxed);
    return 1;
}

static int skip_wire(const int64_t *wire, size_t length, size_t *offset)
{
    size_t remaining = 1;
    while (remaining) {
        if (*offset >= length) return 0;
        int64_t tag = wire[(*offset)++];
        --remaining;
        size_t fields = 0, children = 0;
        switch (tag) {
            case HT_VAR: fields = 4; break;
            case HT_CONST: fields = 2; break;
            case HT_APP: fields = 1; children = 2; break;
            case HT_INDEX: fields = 1; break;
            case HT_LAM: fields = 1; children = 1; break;
            case HT_TYPED_LAM: fields = 1; children = 2; break;
            case HT_TYPED_VAR: fields = 4; children = 1; break;
            case HT_TYPED_NOMINAL: fields = 3; children = 1; break;
            case HT_NOMINAL: fields = 3; break;
            case HT_NAT:
                if (*offset >= length || wire[*offset] <= 0 || (uint64_t) wire[*offset] > length - *offset - 1) return 0;
                fields = (size_t) wire[(*offset)++] ;
                break;
            case HT_WILD: break;
            default: return 0;
        }
        if (fields > length - *offset || children > SIZE_MAX - remaining) return 0;
        *offset += fields;
        remaining += children;
    }
    return 1;
}

/* Makes one assignment in the store as it is. 1: it is made, or its target
    * does not exist (ASSIGNMENT_GONE); 0: it does not hold here; -1: the store
    * failed. */
static int make_assignment(HolV2Machine *m, Assignment *assignment)
{
    HTerm target = ht_lookup_uid(m->terms, assignment->target);
    if (target == HT_NONE) { assignment->state = ASSIGNMENT_GONE; return 1; }
    assignment->state = ASSIGNMENT_OPEN;
    size_t at = 0;
    HTerm value = ht_import_restored(m->terms, assignment->wire, assignment->length, &at);
    if (!term_ok(m, value)) return -1;
    int unified = ht_assign_checked(m->terms, target, value);
    if (unified < 0) { fail(m, ht_error(m->terms)); return -1; }
    if (!unified) return 0;
    HTCheckpoint now = ht_checkpoint(m->terms);
    assignment->state = ASSIGNMENT_MADE;
    assignment->trail = now.trail;
    assignment->heap = now.heap;
    m->assignment_dirty = 1;
    return 1;
}

/* The store has just been restored to the checkpoint of sizes (trail, heap),
    * or it is as it was and these are its sizes. Every assignment that the
    * restore undid, or that was not made yet, is made, in the order in which
    * the host gave them. One whose binding is still there costs two
    * comparisons, and none is looked at when all of them are there: a search
    * step does not pay for the assignments of the run. An assignment whose
    * target does not exist is skipped; the value of another one can bring that
    * target back, so the missing targets are looked up again after one was
    * made. 0: an assignment does not hold in this state, or the store failed. */
static int apply_assignments(HolV2Machine *m, size_t trail, size_t heap)
{
    if (!m->assignment_count) return 1;
    if (m->assignment_settled && trail >= m->assignment_trail && heap >= m->assignment_heap) return 1;
    int held = 1, made = 0;
    for (size_t i = 0; i < m->assignment_count; ++i) {
        Assignment *assignment = &m->assignments[i];
        if (assignment->state == ASSIGNMENT_MADE && trail >= assignment->trail && heap >= assignment->heap) continue;
        assignment->state = ASSIGNMENT_OPEN;
        if (!held) continue;
        int status = make_assignment(m, assignment);
        if (status < 0) return 0;
        if (!status) held = 0;
        else if (assignment->state == ASSIGNMENT_MADE) made = 1;
    }
    while (held && made) {
        made = 0;
        for (size_t i = 0; held && i < m->assignment_count; ++i) {
            Assignment *assignment = &m->assignments[i];
            if (assignment->state != ASSIGNMENT_GONE) continue;
            int status = make_assignment(m, assignment);
            if (status < 0) return 0;
            if (!status) held = 0;
            else if (assignment->state == ASSIGNMENT_MADE) made = 1;
        }
    }
    m->assignment_settled = 1;
    m->assignment_trail = 0;
    m->assignment_heap = 0;
    for (size_t i = 0; i < m->assignment_count; ++i) {
        Assignment assignment = m->assignments[i];
        if (assignment.state == ASSIGNMENT_OPEN) m->assignment_settled = 0;
        if (assignment.state != ASSIGNMENT_MADE) continue;
        if (assignment.trail > m->assignment_trail) m->assignment_trail = assignment.trail;
        if (assignment.heap > m->assignment_heap) m->assignment_heap = assignment.heap;
    }
    return held;
}

int hol_v2_assign(HolV2Machine *m, const int64_t *bindings, size_t length)
{
    if (!m || m->error[0]) return -1;
    if (m->event_kind == HV2_EVENT_STEP_FAILED) {
        m->api_code = HV2_ERROR_USAGE; m->api_error = "A failed V2 proof step must be restored before assignment";
        return -1;
    }
    if (!bindings || !length || bindings[0] < 0) { fail(m, "Invalid V2 persistent assignment"); return -1; }
    size_t at = 1;
    uint64_t count = (uint64_t) bindings[0];
    for (uint64_t i = 0; i < count; ++i) {
        if (at >= length || bindings[at] != HT_VAR || length - at < 5 || bindings[at + 1] < 0) {
            fail(m, "V2 assignment target is not a variable");
            return -1;
        }
        uint64_t uid = (uint64_t) bindings[at + 1];
        HTerm target = ht_lookup_uid(m->terms, uid);
        if (target == HT_NONE || ht_view(m->terms, target).tag != HT_VAR) { fail(m, "Unknown V2 assignment target"); return -1; }
        ht_pin(m->terms, target);
        at += 5;
        HTerm value = ht_import(m->terms, bindings, length, &at);
        if (!term_ok(m, value)) return -1;
        int64_t *wire = NULL;
        size_t wire_count = 0;
        if (!ht_export_managed(m->terms, value, &wire, &wire_count)) { fail(m, ht_error(m->terms)); return -1; }
        if (!reserve(m, m->assignments, &m->assignment_capacity, m->assignment_count + 1, sizeof(*m->assignments))) {
            hm_free(wire);
            return -1;
        }
        m->assignments[m->assignment_count++] = (Assignment) { uid, wire, wire_count, 0, 0, ASSIGNMENT_OPEN };
        m->assignment_settled = 0;
    }
    if (at != length) { fail(m, "Trailing V2 assignment words"); return -1; }
    HTCheckpoint now = ht_checkpoint(m->terms);
    if (!apply_assignments(m, now.trail, now.heap)) {
        if (m->error[0]) return -1;
        m->action = ACTION_FAIL;
        m->assignment_failed = 1;
        m->answer_ready = 0;
        m->resume_answer = 0;
    }
    return 1;
}

int hol_v2_set_work_limit(HolV2Machine *m, uint64_t visits)
{
    if (!m) return -1;
    if (!visits) { m->api_code = HV2_ERROR_USAGE; m->api_error = "V2 atomic work limit must be positive"; return -1; }
    if (!ht_set_work_limit(m->terms, visits)) { m->api_error = ht_error(m->terms); return -1; }
    m->api_code = HV2_ERROR_NONE; m->api_error = NULL;
    return 1;
}

uint64_t hol_v2_work_limit(const HolV2Machine *m)
{
    return m ? ht_work_limit(m->terms) : 0;
}

int hol_v2_error_code(const HolV2Machine *m)
{
    if (!m) return HV2_ERROR_ALLOCATION;
    if (m->error_code) return m->error_code;
    if (m->terms && ht_error_code(m->terms) == HT_ERROR_WORK) return HV2_ERROR_WORK;
    if (atomic_load_explicit(&m->memory->fault, memory_order_relaxed) == 1) return HV2_ERROR_MEMORY;
    if (m->error[0]) return HV2_ERROR_INTERNAL;
    return m->api_error ? (m->api_code ? m->api_code : HV2_ERROR_USAGE) : HV2_ERROR_NONE;
}

int hol_v2_set_memory_limit(HolV2Machine *m, uint64_t bytes)
{
    if (!m) return -1;
    if (bytes > SIZE_MAX) return api_failure(m, HV2_ERROR_USAGE, "Native memory limit exceeds addressable range");
    atomic_store_explicit(&m->memory->limit, (size_t) bytes, memory_order_relaxed);
    atomic_store_explicit(&m->memory->fault, 0, memory_order_relaxed);
    m->api_code = HV2_ERROR_NONE; m->api_error = NULL;
    return 1;
}

uint64_t hol_v2_memory_limit(const HolV2Machine *m)
{
    return m ? atomic_load_explicit(&m->memory->limit, memory_order_relaxed) : 0;
}

void hol_v2_set_counting(HolV2Machine *m, int enabled)
{
    if (m) atomic_store_explicit(&m->memory->counting, enabled != 0, memory_order_relaxed);
}

int hol_v2_stats(const HolV2Machine *m, uint64_t *values, size_t count)
{
    if (!m || !values || count < HV2_STATS_COUNT) return -1;
    values[0] = atomic_load_explicit(&m->memory->bytes, memory_order_relaxed);
    values[1] = atomic_load_explicit(&m->memory->peak, memory_order_relaxed);
    values[2] = ht_heap_count(m->terms);
    values[3] = ht_sealed(m->terms);
    values[4] = m->collections;
    for (size_t i = 0; i < HM_COUNTERS; ++i) values[5 + i] = atomic_load_explicit(&m->memory->counters[i], memory_order_relaxed);
    return 1;
}

void hol_v2_set_legacy_copy(HolV2Machine *m, int enabled)
{
    if (m) m->legacy_copy = enabled != 0;
}

void hol_v2_set_scoped_exports(HolV2Machine *m, int enabled)
{
    if (m) m->scoped_exports = enabled != 0;
}

int hol_v2_set_debug_focus(HolV2Machine *m, const uint64_t *symbols, size_t count, int enabled)
{
    if (!m || m->error[0]) return -1;
    if ((count && !symbols) || (!enabled && count)) return api_failure(m, HV2_ERROR_USAGE, "Invalid debugger focus");
    for (size_t i = 0; i < count; ++i) if (symbols[i] >= m->symbol_count) return api_failure(m, HV2_ERROR_USAGE, "Debugger focus names an unknown symbol");
    size_t *focus = count ? hm_calloc(m->memory, count, sizeof(*focus)) : NULL;
    if (count && !focus) return api_failure(m, HV2_ERROR_MEMORY, "Out of memory for the debugger focus");
    for (size_t i = 0; i < count; ++i) focus[i] = (size_t) symbols[i];
    hm_free(m->focus);
    m->focus = focus;
    m->focus_count = count;
    m->focused = enabled != 0;
    m->api_error = NULL;
    m->api_code = HV2_ERROR_NONE;
    return 1;
}

int hol_v2_set_query_witnesses(HolV2Machine *m, const uint64_t *slots, size_t count)
{
    if (!m || m->error[0]) return -1;
    if ((count && !slots) || count > m->query_count || m->scoped_exports) {
        return api_failure(m, HV2_ERROR_USAGE, "Invalid legacy terminal query slots");
    }
    for (size_t i = 0; i < count; ++i) {
        if (slots[i] >= m->query_count) return api_failure(m, HV2_ERROR_USAGE, "Legacy terminal query slot is out of range");
        HTView variable = ht_view(m->terms, m->query[slots[i]]);
        if (variable.tag != HT_VAR || variable.is_type || variable.a != HT_NONE) {
            return api_failure(m, HV2_ERROR_USAGE, "Legacy terminal query slot is not a fresh term variable");
        }
    }
    for (size_t i = 0; i < count; ++i) {
        if (!ht_mark_query_witness(m->terms, m->query[slots[i]])) return api_failure(m, HV2_ERROR_INTERNAL, "Legacy terminal query slot could not be marked");
    }
    m->api_error = NULL;
    m->api_code = HV2_ERROR_NONE;
    return 1;
}

HolV2Machine *hol_v2_program_mark(HolV2Machine *m)
{
    return m && leave_run(m) ? hol_v2_clone(m) : NULL;
}

int hol_v2_program_truncate(HolV2Machine *m, const HolV2Machine *mark)
{
    if (!m || !mark) return -1;
    if (m->engine_origin != mark->engine_origin) {
        m->api_code = HV2_ERROR_USAGE; m->api_error = "Program mark belongs to a different V2 engine";
        return -1;
    }
    ProgramVersion *version = m->version;
    while (version && version != mark->version) version = version->parent;
    if (!version || mark->error[0]) {
        m->api_code = HV2_ERROR_USAGE; m->api_error = "Program mark is not an ancestor of this V2 program";
        return -1;
    }
    HolV2Machine *copy = clone_in(mark, m->memory);
    if (!copy) {
        int fault = atomic_load_explicit(&m->memory->fault, memory_order_relaxed);
        return api_failure(m, fault == 1 ? HV2_ERROR_MEMORY : HV2_ERROR_ALLOCATION, "V2 program truncate allocation failed");
    }
    uint64_t limit = ht_work_limit(m->terms);
    if (!leave_run(copy) || !ht_set_work_limit(copy->terms, limit)) {
        int result = api_failure(m, hol_v2_error_code(copy), hol_v2_error(copy));
        hol_v2_destroy(copy);
        return result;
    }
    release_fields(m);
    *m = *copy;
    if (copy->api_error == copy->api_message) m->api_error = m->api_message;
    hm_free(copy);
    hm_release(m->memory);
    atomic_store_explicit(&m->memory->fault, 0, memory_order_relaxed);
    return 1;
}

/* Call at collection boundaries: work/hypothesis arrays are then compact.
    * Snapshots retain their own host maps independently of these live roots. */
size_t hol_v2_live_tokens_size(HolV2Machine *m)
{
    if (!m || m->error[0]) return 0;
    m->buffer_count = 0;
    if (!push_word(m, (int64_t) (m->choice_count + 1)) || !push_word(m, (int64_t) m->host_state)) return 0;
    for (size_t i = 0; i < m->choice_count; ++i) if (!push_word(m, (int64_t) m->choices[i].checkpoint.host)) return 0;
    size_t count_at = m->buffer_count, count = 1;
    if (!push_word(m, 0) || !push_word(m, (int64_t) m->current.premises)) return 0;
    for (size_t i = 0; i < m->work_count; ++i) {
        if (!push_word(m, (int64_t) m->work[i].premises)) return 0;
        ++count;
    }
    if (m->action == ACTION_SEARCH) {
        if (!push_word(m, (int64_t) m->search.frame.premises)) return 0;
        ++count;
    }
    for (size_t i = 0; i < m->choice_count; ++i) if (m->choices[i].kind) {
        if (!push_word(m, (int64_t) m->choices[i].search.frame.premises)) return 0;
        ++count;
    }
    m->buffer[count_at] = (int64_t) count;
    return m->buffer_count;
}

size_t hol_v2_live_views_size(HolV2Machine *m)
{
    if (!m || m->error[0]) return 0;
    m->buffer_count = 0;
    if (!push_word(m, (int64_t) (m->choice_count + 1)) || !push_word(m, (int64_t) m->view_token)) return 0;
    for (size_t i = 0; i < m->choice_count; ++i) if (!push_word(m, (int64_t) m->choices[i].checkpoint.view)) return 0;
    return m->buffer_count;
}

size_t hol_v2_live_identities_size(HolV2Machine *m)
{
    if (!m || m->error[0]) return 0;
    m->buffer_count = 0;
    if (!push_word(m, 0)) return 0;
    size_t heap = ht_heap_count(m->terms);
    for (size_t i = ht_sealed(m->terms); i < heap; ++i) {
        HTView term = ht_view(m->terms, i);
        if ((term.tag == HT_VAR || term.tag == HT_NOMINAL) && !push_word(m, (int64_t) term.uid)) return 0;
    }
    m->buffer[0] = (int64_t) m->buffer_count - 1;
    return m->buffer_count;
}

size_t hol_v2_retired_tokens_size(HolV2Machine *m)
{
    if (!m || m->error[0]) return 0;
    m->buffer_count = 0;
    if (!push_word(m, (int64_t) (m->retired_count / 2))) return 0;
    for (size_t i = 0; i < m->retired_count; ++i) if (!push_word(m, (int64_t) m->retired_tokens[i])) return 0;
    m->retired_count = 0;
    return m->buffer_count;
}
