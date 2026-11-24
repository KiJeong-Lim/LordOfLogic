#include "term.h"
#include "native_memory.h"
#include "native_vector.h"
#include "sha256.h"

#include <limits.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>

#define UID_EMPTY UINT64_MAX
#define WORK_LIMIT UINT64_C(5000000)

/* A stable node has no variable, wildcard or opaque constant below it, so no
    * binding can change it. Its summary is exact: whether it is beta-normal,
    * whether it is eta-normal, whether an arithmetic constant occurs in it, the
    * largest scope of its nominals (scope), one more than its largest loose index
    * (open), and its loose indices below 32 that certainly occur (mask). */
enum { HS_STABLE = 1, HS_BETA = 2, HS_ETA = 4, HS_ARITHMETIC = 8, HS_RIGID_HEAD = 16 };
/* A form of normalize alone: the full normal form of a term that is known to
    * be weak-head normal and no abstraction. */
enum { FORM_SPINE = HT_NF + 1 };
enum { MARK_OPAQUE = 1, MARK_ARITHMETIC = 2, MARK_TYPE = 4 };
#define HS_NORMAL (HS_STABLE | HS_BETA | HS_ETA)
#define OPEN_UNKNOWN UINT32_MAX

/* The elements of a closed list of constants, which the cells of every
    * occurrence of a string literal share. The hash of an element covers the
    * elements from it on. */
typedef struct { size_t symbol; uint64_t hash; } StringChar;

struct HTStringBuffer {
    _Atomic size_t references;
    size_t cons, nil, type, count;
    StringChar chars[];
};

/* An application that is a cell of a string literal keeps its buffer in
    * digits and the offset of its element in uid; any other application has
    * neither. A lambda, variable or nominal keeps its optional exact type in b.
    * A cell is an ordinary application in every other respect: only
    * equal reads the two, to compare without a traversal. */
typedef struct {
    int tag;
    /* pinned bit0 is a durable host handle; bit1 watches service deltas;
        * bit2 preserves a legacy terminal query's existential witness.
        * Neither a watch nor a witness flag is a collection root. */
    unsigned char is_type, ground, pinned, summary;
    HTerm a, b;
    uint64_t uid;
    size_t scope;
    int64_t meta;
    char *digits;
    uint32_t open, mask;
} TermNode;

/* Only pages without identities can be shared: unification, trailing and
    * durable variable handles can then always update an identity in place.
    * The final partial page may also be shared; appending detaches that page. */
enum { PAGE_NODES = 256, FIRST_NODES = 512 };
typedef struct {
    _Atomic size_t references;
    size_t used, capacity;
    int identities;
    TermNode nodes[];
} TermPage;

typedef struct {
    /* The initial private block also serves small queries and preserves
        * single-node allocations under tight budgets. */
    TermNode *first;
    size_t first_used, first_capacity;
    TermPage **pages;
    size_t count, capacity;
} TermArena;

typedef struct PayloadSet {
    _Atomic size_t references;
    struct PayloadSet *left, *right;
    HTStringBuffer *buffer;
    uintptr_t key;
    unsigned bit;
    size_t bytes;
} PayloadSet;

typedef struct {
    _Atomic size_t references;
    size_t count, bytes, natural_bytes, max_symbol;
    HvVector nodes;
    PayloadSet *strings;
} TermPrefix;

static HTStringBuffer *string_of(TermNode n)
{
    return (HTStringBuffer *) n.digits;
}

void ht_string_release(HTStringBuffer *buffer)
{
    if (buffer && atomic_fetch_sub_explicit(&buffer->references, 1, memory_order_acq_rel) == 1) {
        hm_free(buffer);
    }
}

/* What a node owns beside itself: the digits of a natural, or one reference
    * to the buffer of a string cell. */
static void release(TermNode n)
{
    if (n.digits) {
        if (n.tag == HT_APP) {
            ht_string_release(string_of(n));
        } else {
            hm_free(n.digits);
        }
    }
}

static void payload_retain(PayloadSet *set)
{
    if (set) atomic_fetch_add_explicit(&set->references, 1, memory_order_relaxed);
}

static void payload_release(PayloadSet *set)
{
    if (!set || atomic_fetch_sub_explicit(&set->references, 1, memory_order_acq_rel) != 1) return;
    payload_release(set->left);
    payload_release(set->right);
    ht_string_release(set->buffer);
    hm_free(set);
}

static PayloadSet *payload_branch(HMemory *memory, unsigned bit, PayloadSet *left, PayloadSet *right)
{
    size_t own = sizeof(HMemoryHeader) + sizeof(PayloadSet);
    if (left->bytes > SIZE_MAX - own || right->bytes > SIZE_MAX - own - left->bytes) return NULL;
    PayloadSet *set = hm_calloc(memory, 1, sizeof(*set));
    if (!set) return NULL;
    atomic_init(&set->references, 1);
    set->bit = bit;
    set->left = left;
    set->right = right;
    set->bytes = own + left->bytes + right->bytes;
    payload_retain(left);
    payload_retain(right);
    return set;
}

/* A persistent compressed binary trie of string-buffer addresses. There is
    * one leaf per buffer; height is bounded by the bits of uintptr_t. */
static PayloadSet *payload_insert_at(HMemory *memory, PayloadSet *old, PayloadSet *leaf, unsigned bit)
{
    if (old->buffer || old->bit < bit) {
        return (leaf->key >> bit) & 1 ? payload_branch(memory, bit, old, leaf) : payload_branch(memory, bit, leaf, old);
    }
    int right = (int) ((leaf->key >> old->bit) & 1);
    PayloadSet *changed = payload_insert_at(memory, right ? old->right : old->left, leaf, bit);
    if (!changed) return NULL;
    PayloadSet *result = right ? payload_branch(memory, old->bit, old->left, changed) : payload_branch(memory, old->bit, changed, old->right);
    payload_release(changed);
    return result;
}

static PayloadSet *payload_insert(HMemory *memory, PayloadSet *old, HTStringBuffer *buffer)
{
    uintptr_t key = (uintptr_t) buffer;
    PayloadSet *found = old;
    while (found && !found->buffer) found = (key >> found->bit) & 1 ? found->right : found->left;
    if (found && found->key == key) { payload_retain(old); return old; }
    PayloadSet *leaf = hm_calloc(memory, 1, sizeof(*leaf));
    if (!leaf) return NULL;
    atomic_init(&leaf->references, 1);
    leaf->buffer = buffer;
    leaf->key = key;
    leaf->bytes = sizeof(HMemoryHeader) * 2 + sizeof(*leaf) + hm_size(buffer);
    atomic_fetch_add_explicit(&buffer->references, 1, memory_order_relaxed);
    if (!old) return leaf;
    uintptr_t difference = key ^ found->key;
    unsigned bit = 0;
    while (difference >>= 1) ++bit;
    PayloadSet *result = payload_insert_at(memory, old, leaf, bit);
    payload_release(leaf);
    return result;
}

static int prefix_copy_node(HMemory *memory, void *target, const void *source)
{
    TermNode original = *(const TermNode *) source;
    TermNode *copy = target;
    *copy = original;
    if (original.digits && original.tag == HT_APP) {
        atomic_fetch_add_explicit(&string_of(original)->references, 1, memory_order_relaxed);
    } else if (original.digits) {
        size_t length = strlen(original.digits) + 1;
        copy->digits = hm_alloc(memory, length);
        if (!copy->digits) return 0;
        memcpy(copy->digits, original.digits, length);
    }
    hm_count(memory, HM_NODES_COPIED, 1);
    return 1;
}

static void prefix_drop_node(void *value)
{
    release(*(TermNode *) value);
}

/* One pending step of a traversal (see enter). */
typedef struct {
    HTerm term, left;
    uint64_t level;
    unsigned char stage, form;
} Frame;

typedef struct { HTerm variable, binding; size_t scope; } Trail;
typedef struct { HTerm left, right; size_t next; } Pending;
typedef struct { uint64_t uid; HTerm term; } Identity;
typedef struct { uint64_t first, end; } RetiredRange;
typedef struct { HTerm left, right; } Equation;
typedef struct { Equation *items; size_t count, capacity; } Equations;
typedef struct { int64_t *items; size_t count, capacity; } Words;
typedef struct { int64_t meta; HTerm type; } Binder;
typedef struct { Binder *items; size_t count, capacity; } Binders;
/* An argument pair that waits while the pairs before it are solved. */
typedef struct { HTerm left, right; size_t binders; uint64_t known; int reduced; } Pair;

typedef struct {
    uint64_t serial, generation;
    size_t variables, scope;
    int rigid, exact, value_types, possible, callable, simple;
    HTerm head_variable;
    uint64_t last_nominal;
    HTerm flex_type;
} OpenMemo;
typedef struct { HTerm term; unsigned stage; OpenMemo left; } MemoFrame;

struct HolTermStore {
    HMemory *memory;
    int error_code;
    TermArena arena;
    TermPrefix *prefix;
    HMemoryLease *prefix_lease;
    size_t base, count;
    Trail *trail;
    size_t trail_count, trail_capacity;
    int transient_wire;
    Pending *pending;
    size_t pending_count, pending_capacity, pending_head;
    Identity *identities;
    size_t identity_capacity, identity_count, identity_peak;
    RetiredRange *retired;
    size_t retired_count, retired_capacity;
    uint64_t next_uid;
    size_t successor, arrow, sealed;
    unsigned char *marks;
    size_t mark_count, mark_capacity;
    uint64_t work, work_limit;
    size_t operations;
    Frame *frames;
    size_t frame_count, frame_capacity;
    Pair *pairs;
    size_t pair_count, pair_capacity;
    /* The buffers of the unifier, kept between two unifications. */
    Equations solving, delayed;
    Binders binders;
    int unifying;
    uint64_t changes;
    int binding_has_loose_indices;
    OpenMemo *memo;
    uint64_t *memo_valid;
    size_t memo_valid_capacity;
    size_t memo_capacity, memo_base;
    uint64_t *memo_changes;
    size_t memo_change_capacity;
    uint64_t memo_serial, memo_generation;
    MemoFrame *memo_frames;
    size_t memo_frame_capacity;
    char error[192];
};

/* Shared program nodes have no variables or nominals and are never written.
    * The private arena starts at base; term handles keep their old indices. */
static inline TermNode *node_at(const HolTermStore *s, size_t index)
{
    if (index < s->base) return (TermNode *) hv_get(&s->prefix->nodes, index);
    size_t relative = index - s->base;
    if (relative < FIRST_NODES) return &s->arena.first[relative];
    return &s->arena.pages[(relative - FIRST_NODES) / PAGE_NODES]->nodes[relative % PAGE_NODES];
}
#define NODE(s,index) (*node_at((s), (index)))

static void release_prefix(TermPrefix *prefix)
{
    if (prefix && atomic_fetch_sub_explicit(&prefix->references, 1, memory_order_acq_rel) == 1) {
        hv_destroy(&prefix->nodes);
        payload_release(prefix->strings);
        hm_free(prefix);
    }
}

static int fail(HolTermStore *s, const char *message);
static int unshare_prefix(HolTermStore *s);
static int private_pages(HolTermStore *s);
static int copy_node(HolTermStore *s, TermNode original, TermNode *copy);

typedef struct { HTerm *items; size_t count, capacity; } Terms;

static int marked(const HolTermStore *s, size_t symbol, unsigned char mark)
{
    return symbol < s->mark_count && (s->marks[symbol] & mark);
}

/* Only immutable, already-normal rigid constructor trees qualify. In
    * particular, a variable currently bound to such a tree does not qualify. */
static int ground_node(const HolTermStore *s, TermNode n)
{
    if (n.tag == HT_NAT) return 1;
    if (n.tag == HT_CONST) return !marked(s, n.a, MARK_OPAQUE);
    if (n.tag != HT_APP || !NODE(s, n.a).ground || !NODE(s, n.b).ground) return 0;
    TermNode function = NODE(s, n.a), argument = NODE(s, n.b);
    return function.tag != HT_CONST || function.a != s->successor || argument.tag != HT_NAT;
}

/* The children of a node precede it, so their summaries are already known. A
    * variable or a nominal keeps its own scope. */
static void summarize(const HolTermStore *s, TermNode *n)
{
    n->ground = ground_node(s, *n);
    n->summary = 0;
    n->open = 0;
    n->mask = 0;
    if (n->tag == HT_VAR) return;
    if (n->tag == HT_NOMINAL) {
        n->summary = HS_NORMAL;
        return;
    }
    n->scope = 0;
    if (n->tag == HT_CONST) {
        if (marked(s, n->a, MARK_OPAQUE)) return;
        n->summary = HS_NORMAL | (n->a == s->successor ? 0 : HS_RIGID_HEAD) | (n->a == s->successor || marked(s, n->a, MARK_ARITHMETIC) ? HS_ARITHMETIC : 0);
    } else if (n->tag == HT_NAT) {
        n->summary = HS_NORMAL;
    } else if (n->tag == HT_INDEX) {
        n->summary = HS_NORMAL;
        n->open = n->a < OPEN_UNKNOWN - 1 ? (uint32_t) n->a + 1 : OPEN_UNKNOWN;
        n->mask = n->a < 32 ? UINT32_C(1) << n->a : 0;
    } else if (n->tag == HT_APP) {
        TermNode f = NODE(s, n->a), x = NODE(s, n->b);
        n->open = f.open > x.open ? f.open : x.open;
        n->summary = f.summary & HS_RIGID_HEAD;
        if (!(f.summary & x.summary & HS_STABLE)) return;
        int redex = f.tag == HT_LAM || (f.tag == HT_CONST && f.a == s->successor && x.tag == HT_NAT);
        n->summary |= (unsigned char) (HS_STABLE | (f.summary & x.summary & (HS_BETA | HS_ETA)) | ((f.summary | x.summary) & HS_ARITHMETIC));
        if (redex) n->summary &= (unsigned char) ~HS_BETA;
        n->scope = f.scope > x.scope ? f.scope : x.scope;
        n->mask = f.mask | x.mask;
    } else if (n->tag == HT_LAM) {
        TermNode body = NODE(s, n->a);
        n->open = body.open == OPEN_UNKNOWN ? OPEN_UNKNOWN : body.open ? body.open - 1 : 0;
        if (n->b != HT_NONE && NODE(s, n->b).open > n->open) n->open = NODE(s, n->b).open;
        if (!(body.summary & HS_STABLE)) return;
        /* body = f #0 is an eta-redex unless #0 certainly occurs in f */
        int redex = body.tag == HT_APP && NODE(s, body.b).tag == HT_INDEX && !NODE(s, body.b).a && !(NODE(s, body.a).mask & 1);
        n->summary = body.summary & (unsigned char) ~HS_RIGID_HEAD;
        if (redex) n->summary &= (unsigned char) ~HS_ETA;
        n->scope = body.scope;
        n->mask = body.mask >> 1;
        if (n->b != HT_NONE) {
            TermNode type = NODE(s, n->b);
            n->summary &= type.summary | HS_ARITHMETIC;
            if (type.scope > n->scope) n->scope = type.scope;
            n->mask |= type.mask;
        }
    }
}

static void memo_mutated(HolTermStore *s, size_t variable);
static void memo_invalidate(HolTermStore *s);
static void memo_release(HolTermStore *s);
static int open_memo(HolTermStore *s, HTerm root, OpenMemo *output);

/* Detaching pages can fail. Change no symbol role or summary until every
    * node that needs a new summary is writable. */
static int prepare_summaries(HolTermStore *s, int include_prefix)
{
    if (include_prefix && !unshare_prefix(s)) return 0;
    return private_pages(s) || fail(s, "Term summary page allocation failed");
}

static void refresh_summaries(HolTermStore *s)
{
    memo_invalidate(s);
    for (size_t i = s->base; i < s->count; ++i) summarize(s, &NODE(s, i));
}

static int stable(TermNode n)
{
    return n.summary & HS_STABLE;
}

static int normal(TermNode n)
{
    return (n.summary & HS_NORMAL) == HS_NORMAL;
}

/* A stable node all of whose loose indices are below limit. */
static int closed_below(TermNode n, size_t limit)
{
    return (n.summary & HS_STABLE) && n.open != OPEN_UNKNOWN && n.open <= limit;
}

static int fail(HolTermStore *s, const char *message)
{
    if (s && !s->error[0]) {
        int fault = atomic_load_explicit(&s->memory->fault, memory_order_relaxed);
        if (fault == 1) { message = "Native memory limit exceeded"; s->error_code = HT_ERROR_MEMORY; }
        else if (fault == 2) s->error_code = HT_ERROR_ALLOCATION;
        else if (!s->error_code) s->error_code = HT_ERROR_INTERNAL;
        size_t length = strlen(message);
        if (length >= sizeof(s->error)) {
            length = sizeof(s->error) - 1;
        }
        memcpy(s->error, message, length);
        s->error[length] = '\0';
    }
    return 0;
}

static void *grow(HolTermStore *s, void *pointer, size_t *capacity, size_t count, size_t width);

/* grow retains the old pointer and capacity on failure. Assign through the
    * caller's typed lvalue: writing a T* through void** is not C11 alias-safe.
    * Arguments are stable lvalues/values without side effects. */
#define reserve(owner,pointer,capacity,count,width) \
    ((count) <= *(capacity) || \
        ((pointer) = grow((owner), (pointer), (capacity), (count), (width)), (count) <= *(capacity)))

static size_t bounded_capacity(HMemory *memory, size_t capacity, size_t count, size_t next, size_t width, size_t header)
{
    size_t limit = atomic_load_explicit(&memory->limit, memory_order_relaxed);
    size_t charged = atomic_load_explicit(&memory->bytes, memory_order_relaxed);
    if (limit && charged <= limit && header <= limit - charged && count > capacity) {
        size_t available = (limit - charged - header) / width;
        size_t required = count - capacity;
        if (next - capacity > available && required <= available) {
            size_t extra = available / 2;
            if (extra < required) extra = required;
            next = capacity + extra;
        }
    }
    return next;
}

static void *grow(HolTermStore *s, void *pointer, size_t *capacity, size_t count, size_t width)
{
    if (!width || count > SIZE_MAX / width) {
        fail(s, "Term allocation size overflow");
        return pointer;
    }
    size_t next = *capacity ? *capacity : 32;
    while (next < count) {
        if (next > SIZE_MAX / 2) {
            next = count;
            break;
        }
        next *= 2;
    }
    if (next > SIZE_MAX / width) {
        next = count;
    }
    /* Geometric spare capacity must not reject a request that fits the cap.
        * Keep half the remaining room for other arrays; hm_realloc still
        * performs the authoritative atomic reservation. No fault is cleared. */
    next = bounded_capacity(s->memory, *capacity, count, next, width, pointer ? 0 : sizeof(HMemoryHeader));
    void *resized = hm_realloc(s->memory, pointer, next * width);
    if (!resized) {
        fail(s, "Term allocation failed");
        return pointer;
    }
    *capacity = next;
    return resized;
}

static int push_term(HolTermStore *s, Terms *terms, HTerm term)
{
    if (term == HT_NONE || terms->count == SIZE_MAX || !reserve(s, terms->items, &terms->capacity, terms->count + 1, sizeof(*terms->items))) {
        return 0;
    }
    terms->items[terms->count++] = term;
    return 1;
}

static int push_binder(HolTermStore *s, Binders *binders, Binder binder)
{
    if (!reserve(s, binders->items, &binders->capacity, binders->count + 1, sizeof(*binders->items))) return 0;
    binders->items[binders->count++] = binder;
    return 1;
}

static int push_word(HolTermStore *s, Words *words, int64_t word)
{
    if (words->count == SIZE_MAX || !reserve(s, words->items, &words->capacity, words->count + 1, sizeof(*words->items))) {
        return 0;
    }
    words->items[words->count++] = word;
    return 1;
}

static void release_page(TermPage *page)
{
    if (atomic_fetch_sub_explicit(&page->references, 1, memory_order_acq_rel) != 1) return;
    for (size_t i = 0; i < page->used; ++i) release(page->nodes[i]);
    hm_free(page);
}

static void release_arena(TermArena *arena)
{
    while (arena->first_used) release(arena->first[--arena->first_used]);
    hm_free(arena->first);
    while (arena->count) release_page(arena->pages[--arena->count]);
    hm_free(arena->pages);
    *arena = (TermArena) { 0 };
}

static TermPage *new_page(HMemory *memory, size_t capacity)
{
    TermPage *page = hm_alloc(memory, sizeof(*page) + capacity * sizeof(TermNode));
    if (page) {
        atomic_init(&page->references, 1);
        page->used = 0;
        page->capacity = capacity;
        page->identities = 0;
    }
    return page;
}

static TermPage *copy_page(HolTermStore *s, const TermPage *old, size_t used, size_t capacity)
{
    TermPage *page = new_page(s->memory, capacity);
    if (!page) return NULL;
    for (; page->used < used; ++page->used) {
        TermNode n = old->nodes[page->used];
        if (!copy_node(s, n, &page->nodes[page->used])) {
            release_page(page);
            return NULL;
        }
        if (n.tag == HT_VAR || n.tag == HT_NOMINAL) page->identities = 1;
    }
    return page;
}

/* Preflight before destructive collection, policy changes or arbitrary pins.
    * Detaching a page changes no handles or ownership visible to callers. */
static int private_page(HolTermStore *s, size_t number)
{
    TermPage *page = s->arena.pages[number];
    size_t used = s->count - s->base - FIRST_NODES - number * PAGE_NODES;
    if (used > page->used) used = page->used;
    if (atomic_load_explicit(&page->references, memory_order_acquire) == 1) {
        while (page->used > used) release(page->nodes[--page->used]);
        return 1;
    }
    TermPage *copy = copy_page(s, page, used, used);
    if (!copy) return 0;
    s->arena.pages[number] = copy;
    release_page(page);
    return 1;
}

static int private_pages(HolTermStore *s)
{
    for (size_t i = 0; i < s->arena.count; ++i) {
        if (!private_page(s, i)) return 0;
    }
    return 1;
}

static int append_node(HolTermStore *s, TermArena *arena, size_t offset, TermNode value)
{
    if (offset < FIRST_NODES) {
        if (!reserve(s, arena->first, &arena->first_capacity, offset + 1, sizeof(value))) return 0;
        arena->first[arena->first_used++] = value;
        return 1;
    }
    size_t number = (offset - FIRST_NODES) / PAGE_NODES, at = offset % PAGE_NODES;
    if (number == arena->count) {
        size_t overhead = sizeof(HMemoryHeader) + sizeof(TermPage);
        if (number == arena->capacity) overhead += sizeof(*arena->pages) + (arena->pages ? 0 : sizeof(HMemoryHeader));
        size_t capacity = bounded_capacity(s->memory, 0, 1, 8, sizeof(TermNode), overhead);
        TermPage *fresh = new_page(s->memory, capacity);
        if (!fresh) return fail(s, "Term page allocation failed");
        if (!reserve(s, arena->pages, &arena->capacity, number + 1, sizeof(*arena->pages))) {
            release_page(fresh);
            return 0;
        }
        arena->pages[arena->count++] = fresh;
    }
    TermPage *page = arena->pages[number];
    size_t capacity = page->capacity;
    if (at >= capacity) capacity = at > PAGE_NODES / 2 ? PAGE_NODES : at ? at * 2 : 1;
    if (atomic_load_explicit(&page->references, memory_order_acquire) > 1) {
        TermPage *copy = copy_page(s, page, at, at + 1);
        if (!copy) return fail(s, "Term page copy allocation failed");
        release_page(page);
        arena->pages[number] = page = copy;
    } else if (capacity > page->capacity) {
        capacity = bounded_capacity(s->memory, page->capacity, at + 1, capacity, sizeof(TermNode), 0);
        TermPage *grown = hm_realloc(s->memory, page, sizeof(*page) + capacity * sizeof(TermNode));
        if (!grown) return fail(s, "Term page growth failed");
        arena->pages[number] = page = grown;
        page->capacity = capacity;
    }
    /* A rollback may have left an immutable suffix owned by another copy.
        * If this is the last owner now, it also owns destruction of that suffix. */
    while (page->used > at) release(page->nodes[--page->used]);
    page->nodes[page->used++] = value;
    if (value.tag == HT_VAR || value.tag == HT_NOMINAL) page->identities = 1;
    return 1;
}

static int copy_range(HolTermStore *s, TermArena *result, size_t first, size_t end)
{
    for (size_t i = first; i < end; ++i) {
        TermNode n;
        if (!copy_node(s, NODE(s, i), &n)) return 0;
        if (!append_node(s, result, i - first, n)) { release(n); return 0; }
    }
    return 1;
}

static void truncate_arena(TermArena *arena, size_t kept, int relocated)
{
    size_t first = kept < FIRST_NODES ? kept : FIRST_NODES;
    if (relocated) arena->first_used = first;
    else while (arena->first_used > first) release(arena->first[--arena->first_used]);
    kept -= first;
    size_t pages = kept / PAGE_NODES + (kept % PAGE_NODES != 0);
    while (arena->count > pages) {
        TermPage *page = arena->pages[--arena->count];
        if (relocated) page->used = 0;
        release_page(page);
    }
    if (kept % PAGE_NODES) {
        TermPage *last = arena->pages[pages - 1];
        if (relocated) last->used = kept % PAGE_NODES;
        else if (atomic_load_explicit(&last->references, memory_order_acquire) == 1) {
            while (last->used > kept % PAGE_NODES) release(last->nodes[--last->used]);
        }
    }
}

static HTerm node(HolTermStore *s, TermNode value)
{
    if (!s || s->error[0] || s->count >= INT64_MAX) return HT_NONE;
    summarize(s, &value);
    HTerm result = s->count;
    if (!append_node(s, &s->arena, result - s->base, value)) return HT_NONE;
    ++s->count;
    hm_count(s->memory, HM_NODES_CREATED, 1);
    size_t offset = result - s->base;
    if (offset / 64 < s->memo_valid_capacity) s->memo_valid[offset / 64] &= ~(UINT64_C(1) << (offset % 64));
    return result;
}

static size_t bucket(uint64_t uid, size_t capacity)
{
    return (size_t) (uid * UINT64_C(11400714819323198485)) & (capacity - 1);
}

static int identity_retired(const HolTermStore *s, uint64_t uid)
{
    size_t first = 0, end = s->retired_count;
    if (!end || uid >= s->retired[end - 1].end) {
        return 0;
    }
    while (first < end) {
        size_t middle = first + (end - first) / 2;
        RetiredRange range = s->retired[middle];
        if (uid < range.first) {
            end = middle;
        } else if (uid >= range.end) {
            first = middle + 1;
        } else {
            return 1;
        }
    }
    return 0;
}

/* Every live identity can add at most one range when rolled back. Reserving
    * that space before allocation keeps retirement allocation-free. */
static int reserve_retired(HolTermStore *s, size_t extra)
{
    if (s->identity_count > SIZE_MAX - s->retired_count || extra > SIZE_MAX - s->retired_count - s->identity_count) {
        return fail(s, "Retired identity table overflow");
    }
    return reserve(s, s->retired, &s->retired_capacity, s->retired_count + s->identity_count + extra, sizeof(*s->retired));
}

static int retire_range(HolTermStore *s, uint64_t first, uint64_t end)
{
    size_t low = 0, high = s->retired_count;
    while (low < high) {
        size_t middle = low + (high - low) / 2;
        if (s->retired[middle].end < first) {
            low = middle + 1;
        } else {
            high = middle;
        }
    }
    size_t after = low;
    while (after < s->retired_count && s->retired[after].first <= end) {
        RetiredRange range = s->retired[after++];
        if (range.first < first) first = range.first;
        if (range.end > end) end = range.end;
    }
    if (after == low) {
        if (s->retired_count == s->retired_capacity) {
            return fail(s, "Missing retired identity capacity");
        }
        memmove(s->retired + low + 1, s->retired + low, (s->retired_count - low) * sizeof(*s->retired));
        ++s->retired_count;
    } else {
        memmove(s->retired + low + 1, s->retired + after, (s->retired_count - after) * sizeof(*s->retired));
        s->retired_count -= after - low - 1;
    }
    s->retired[low] = (RetiredRange) { first, end };
    return 1;
}

static int rehash_identities(HolTermStore *s, size_t capacity)
{
    Identity *table = hm_alloc(s->memory, capacity * sizeof(*table));
    if (!table) {
        return 0;
    }
    for (size_t i = 0; i < capacity; ++i) {
        table[i] = (Identity) { UID_EMPTY, HT_NONE };
    }
    for (size_t i = 0; i < s->identity_capacity; ++i) {
        Identity entry = s->identities[i];
        if (entry.uid == UID_EMPTY) {
            continue;
        }
        size_t index = bucket(entry.uid, capacity);
        while (table[index].uid != UID_EMPTY) {
            index = (index + 1) & (capacity - 1);
        }
        table[index] = entry;
    }
    hm_free(s->identities);
    s->identities = table;
    s->identity_capacity = capacity;
    return 1;
}

static int reserve_identities(HolTermStore *s)
{
    if (s->identity_capacity && s->identity_count < s->identity_capacity / 2) {
        return 1;
    }
    size_t capacity = s->identity_capacity ? s->identity_capacity * 2 : 64;
    if (capacity < s->identity_capacity || capacity > SIZE_MAX / sizeof(Identity)) {
        return fail(s, "Term identity table overflow");
    }
    return rehash_identities(s, capacity) || fail(s, "Term identity allocation failed");
}

static int insert_identity(HolTermStore *s, uint64_t uid, HTerm term, int restoring)
{
    if (!restoring && identity_retired(s, uid)) {
        return fail(s, "Term wire refers to an expired identity");
    }
    if (!reserve_identities(s) || !reserve_retired(s, 1)) {
        return 0;
    }
    size_t index = bucket(uid, s->identity_capacity);
    while (s->identities[index].uid != UID_EMPTY) {
        if (s->identities[index].uid == uid) {
            return fail(s, "Duplicate term identity");
        }
        index = (index + 1) & (s->identity_capacity - 1);
    }
    s->identities[index] = (Identity) { uid, term };
    if (++s->identity_count > s->identity_peak) {
        s->identity_peak = s->identity_count;
    }
    return 1;
}

/* The uids are sorted. Every one of them is live, so the ranges have room for
    * them (reserve_retired); a pass from the largest down merges them in place.
    * Retiring them one by one would move the ranges above each of them. */
static void retire_sorted_from(HolTermStore *s, const void *uids, size_t count, size_t stride)
{
    RetiredRange *ranges = s->retired;
    size_t total = s->retired_count + count, write = total, i = s->retired_count, j = count;
    if (!count) {
        return;
    }
    while (i || j) {
        RetiredRange next;
        uint64_t uid = 0;
        if (j) memcpy(&uid, (const unsigned char *) uids + (j - 1) * stride, sizeof(uid));
        if (j && (!i || uid >= ranges[i - 1].first)) {
            --j;
            next = (RetiredRange) { uid, uid + 1 };
        } else {
            next = ranges[--i];
        }
        if (write < total && next.end >= ranges[write].first) {
            ranges[write].first = next.first;
            if (next.end > ranges[write].end) {
                ranges[write].end = next.end;
            }
        } else {
            ranges[--write] = next;
        }
    }
    memmove(ranges, ranges + write, (total - write) * sizeof(*ranges));
    s->retired_count = total - write;
}

static int ascending(const void *left, const void *right)
{
    uint64_t a = *(const uint64_t *) left, b = *(const uint64_t *) right;
    return a < b ? -1 : a > b;
}

/* retire is 0 when the caller retires the uid itself (retire_sorted). */
static void remove_identity(HolTermStore *s, uint64_t uid, int retire)
{
    if (!s->identity_capacity) {
        return;
    }
    size_t index = bucket(uid, s->identity_capacity);
    while (s->identities[index].uid != UID_EMPTY) {
        if (s->identities[index].uid == uid) {
            if (retire && !retire_range(s, uid, uid + 1)) {
                return;
            }
            --s->identity_count;
            size_t mask = s->identity_capacity - 1;
            size_t next = (index + 1) & mask;
            while (s->identities[next].uid != UID_EMPTY) {
                size_t home = bucket(s->identities[next].uid, s->identity_capacity);
                if (((next - home) & mask) >= ((index - home) & mask)) {
                    s->identities[index] = s->identities[next];
                    index = next;
                }
                next = (next + 1) & mask;
            }
            s->identities[index] = (Identity) { UID_EMPTY, HT_NONE };
            return;
        }
        index = (index + 1) & (s->identity_capacity - 1);
    }
}

HolTermStore *ht_create_in(HMemory *memory)
{
    HolTermStore *s = hm_calloc(memory, 1, sizeof(*s));
    if (s) {
        hm_retain(memory);
        s->memory = memory;
        s->memo_generation = 1;
        s->successor = HT_NONE;
        s->arrow = HT_NONE;
        s->pending_head = HT_NONE;
        s->work_limit = WORK_LIMIT;
    }
    return s;
}

HolTermStore *ht_create(void)
{
    HMemory *memory = hm_create();
    if (!memory) return NULL;
    HolTermStore *store = ht_create_in(memory);
    hm_release(memory);
    return store;
}

HMemory *ht_memory(const HolTermStore *s)
{
    return s ? s->memory : NULL;
}

void ht_destroy(HolTermStore *s)
{
    if (!s) {
        return;
    }
    release_arena(&s->arena);
    release_prefix(s->prefix);
    hm_lease_release(s->prefix_lease);
    hm_free(s->trail);
    hm_free(s->pending);
    hm_free(s->identities);
    hm_free(s->retired);
    hm_free(s->marks);
    memo_release(s);
    hm_free(s->frames);
    hm_free(s->pairs);
    hm_free(s->solving.items);
    hm_free(s->delayed.items);
    hm_free(s->binders.items);
    HMemory *memory = s->memory;
    hm_free(s);
    hm_release(memory);
}

int ht_error_code(const HolTermStore *s)
{
    return s ? s->error_code : HT_ERROR_ALLOCATION;
}

const char *ht_error(const HolTermStore *s)
{
    return s ? s->error : "Term store allocation failed";
}

size_t ht_heap_count(const HolTermStore *s)
{
    return s ? s->count : 0;
}

HTCheckpoint ht_checkpoint(const HolTermStore *s)
{
    return (HTCheckpoint) { s->count, s->trail_count, s->pending_count, s->pending_head };
}

int ht_restore(HolTermStore *s, HTCheckpoint saved)
{
    if (!s || saved.heap > s->count || saved.trail > s->trail_count || saved.pending > s->pending_count || (saved.pending_head != HT_NONE && saved.pending_head >= saved.pending)) {
        return fail(s, "Invalid term checkpoint");
    }
    if (saved.heap < s->base && !unshare_prefix(s)) return 0;
    while (s->trail_count > saved.trail) {
        Trail old = s->trail[--s->trail_count];
        NODE(s, old.variable).a = old.binding;
        NODE(s, old.variable).scope = old.scope;
        memo_mutated(s, old.variable);
    }
    while (s->count > saved.heap) {
        size_t offset = s->count - s->base - 1;
        if (offset >= FIRST_NODES && !s->arena.pages[(offset - FIRST_NODES) / PAGE_NODES]->identities) {
            size_t first = s->count - 1 - offset % PAGE_NODES;
            s->count = first < saved.heap ? saved.heap : first;
            continue;
        }
        TermNode old = NODE(s, --s->count);
        if (old.tag == HT_VAR || old.tag == HT_NOMINAL) {
            remove_identity(s, old.uid, 1);
        }
    }
    truncate_arena(&s->arena, saved.heap - s->base, 0);
    if (s->sealed > s->count) {
        s->sealed = s->count;
    }
    s->pending_count = saved.pending;
    s->pending_head = saved.pending_head;
    return 1;
}

static void *release_spare(void *pointer, size_t *capacity, size_t count, size_t limit)
{
    if (!count && *capacity > limit) {
        hm_free(pointer);
        pointer = NULL;
        *capacity = 0;
    }
    return pointer;
}

int ht_reset(HolTermStore *s, size_t heap, uint64_t next_uid, size_t symbols)
{
    if (!s || s->error[0] || s->operations || next_uid > s->next_uid) {
        return fail(s, "Invalid term store reset");
    }
    if (!ht_restore(s, (HTCheckpoint) { heap, 0, 0, HT_NONE })) {
        return 0;
    }
    memo_release(s);
    while (s->retired_count && s->retired[s->retired_count - 1].first >= next_uid) {
        --s->retired_count;
    }
    if (s->retired_count && s->retired[s->retired_count - 1].end > next_uid) {
        s->retired[s->retired_count - 1].end = next_uid;
    }
    s->next_uid = next_uid;
    if (s->arrow >= symbols) s->arrow = HT_NONE;
    if (s->mark_count > symbols) {
        s->mark_count = symbols;
    }
    s->work_limit = WORK_LIMIT;
    s->work = 0;
    s->frame_count = 0;
    s->identity_peak = s->identity_count;
    if (s->identity_capacity / 8 > s->identity_count && s->identity_capacity > 64) {
        size_t capacity = 64;
        while (capacity / 4 < s->identity_count) {
            capacity *= 2;
        }
        rehash_identities(s, capacity);
    }
    s->trail = release_spare(s->trail, &s->trail_capacity, s->trail_count, 4096);
    s->pending = release_spare(s->pending, &s->pending_capacity, s->pending_count, 4096);
    s->retired = release_spare(s->retired, &s->retired_capacity, s->retired_count, 4096);
    s->frames = release_spare(s->frames, &s->frame_capacity, s->frame_count, 4096);
    s->pair_count = 0;
    s->pairs = release_spare(s->pairs, &s->pair_capacity, 0, 4096);
    s->solving.items = release_spare(s->solving.items, &s->solving.capacity, 0, 4096);
    s->delayed.items = release_spare(s->delayed.items, &s->delayed.capacity, 0, 4096);
    s->binders.items = release_spare(s->binders.items, &s->binders.capacity, 0, 4096);
    return 1;
}

static int copy_node(HolTermStore *s, TermNode original, TermNode *copy)
{
    *copy = original;
    if (original.digits && original.tag == HT_APP) {
        if (hm_owner(original.digits) == s->memory) atomic_fetch_add_explicit(&string_of(original)->references, 1, memory_order_relaxed);
        else copy->digits = NULL;
    } else if (original.digits) {
        size_t length = strlen(original.digits) + 1;
        copy->digits = hm_alloc(s->memory, length);
        if (!copy->digits) return 0;
        memcpy(copy->digits, original.digits, length);
    }
    hm_count(s->memory, HM_NODES_COPIED, 1);
    return 1;
}

static int unshare_prefix(HolTermStore *s)
{
    if (!s->base) return 1;
    TermArena arena = { 0 };
    if (!copy_range(s, &arena, 0, s->count)) {
        release_arena(&arena);
        return fail(s, "Term program copy allocation failed");
    }
    release_arena(&s->arena);
    s->arena = arena;
    release_prefix(s->prefix);
    hm_lease_release(s->prefix_lease);
    s->prefix_lease = NULL;
    s->base = 0;
    s->prefix = NULL;
    return 1;
}

size_t ht_seal(HolTermStore *s)
{
    while (s->sealed < s->count && NODE(s, s->sealed).tag != HT_VAR && NODE(s, s->sealed).tag != HT_NOMINAL) ++s->sealed;
    if (s->base == s->sealed || !s->sealed) return s->sealed;
    size_t added = s->sealed - s->base;
    TermPrefix *prefix = hm_calloc(s->memory, 1, sizeof(*prefix));
    TermArena arena = { 0 };
    if (!prefix || !copy_range(s, &arena, s->sealed, s->count)) {
        hm_free(prefix);
        release_arena(&arena);
        fail(s, "Term program allocation failed");
        return s->sealed;
    }
    atomic_init(&prefix->references, 1);
    if (s->prefix) {
        hv_clone(&prefix->nodes, &s->prefix->nodes, s->memory);
        prefix->strings = s->prefix->strings;
        payload_retain(prefix->strings);
        prefix->natural_bytes = s->prefix->natural_bytes;
        prefix->max_symbol = s->prefix->max_symbol;
    } else hv_init(&prefix->nodes, s->memory, sizeof(TermNode), prefix_copy_node, prefix_drop_node);
    int success = 1;
    for (size_t i = 0; success && i < added; ++i) {
        TermNode n = NODE(s, s->base + i);
        if (n.tag == HT_CONST && n.a > prefix->max_symbol) prefix->max_symbol = n.a;
        if (n.digits && n.tag == HT_APP) {
            PayloadSet *next = payload_insert(s->memory, prefix->strings, string_of(n));
            if (!next) success = 0;
            else { payload_release(prefix->strings); prefix->strings = next; }
        } else if (n.digits) {
            size_t bytes = sizeof(HMemoryHeader) + hm_size(n.digits);
            if (bytes > SIZE_MAX - prefix->natural_bytes) success = 0;
            else prefix->natural_bytes += bytes;
        }
        if (success) success = hv_append(&prefix->nodes, &n);
    }
    if (!success) {
        release_prefix(prefix);
        release_arena(&arena);
        fail(s, "Term program append allocation failed");
        return s->sealed;
    }
    prefix->count = s->sealed;
    size_t bytes = sizeof(HMemoryHeader) + sizeof(*prefix) + hv_bytes(&prefix->nodes);
    size_t payloads = prefix->strings ? prefix->strings->bytes : 0;
    if (prefix->natural_bytes > SIZE_MAX - bytes || payloads > SIZE_MAX - bytes - prefix->natural_bytes) {
        release_prefix(prefix);
        release_arena(&arena);
        fail(s, "Term program payload size overflow");
        return s->sealed;
    }
    prefix->bytes = bytes + prefix->natural_bytes + payloads;
    release_arena(&s->arena);
    release_prefix(s->prefix);
    s->prefix = prefix;
    s->arena = arena;
    s->base = s->sealed;
    return s->sealed;
}

size_t ht_sealed(const HolTermStore *s)
{
    return s->sealed;
}

uint64_t ht_next_uid(const HolTermStore *s)
{
    return s->next_uid;
}

int ht_advance_uid(HolTermStore *s, uint64_t next_uid)
{
    if (next_uid > INT64_MAX) {
        return fail(s, "Term identity overflow");
    }
    if (s->next_uid < next_uid) {
        s->next_uid = next_uid;
    }
    return 1;
}

int ht_preserve_identity_history(HolTermStore *restored, const HolTermStore *live)
{
    if (!restored || !live || restored->error[0]) {
        return fail(restored, "Invalid term identity history");
    }
    if (restored == live) {
        return 1;
    }
    for (size_t i = 0; i < live->retired_count; ++i) {
        RetiredRange range = live->retired[i];
        if (!reserve_retired(restored, 1) || !retire_range(restored, range.first, range.end)) {
            return 0;
        }
    }
    size_t private_count = live->count - live->base;
    int table = live->identity_capacity <= private_count;
    size_t count = table ? live->identity_capacity : private_count;
    for (size_t i = 0; i < count; ++i) {
        uint64_t uid;
        if (table) {
            uid = live->identities[i].uid;
            if (uid == UID_EMPTY) continue;
        } else {
            TermNode node = NODE(live, live->base + i);
            if (node.tag != HT_VAR && node.tag != HT_NOMINAL) continue;
            uid = node.uid;
        }
        int present = 0;
        if (restored->identity_capacity) {
            size_t index = bucket(uid, restored->identity_capacity);
            while (restored->identities[index].uid != UID_EMPTY) {
                if (restored->identities[index].uid == uid) {
                    present = 1;
                    break;
                }
                index = (index + 1) & (restored->identity_capacity - 1);
            }
        }
        if (!present && (!reserve_retired(restored, 1) || !retire_range(restored, uid, uid + 1))) {
            return 0;
        }
    }
    return ht_advance_uid(restored, live->next_uid);
}

static void history_sift(Identity *entries, size_t count, size_t root)
{
    while (root < count / 2) {
        size_t child = root * 2 + 1;
        if (child + 1 < count && entries[child].uid < entries[child + 1].uid) ++child;
        if (entries[root].uid >= entries[child].uid) break;
        Identity entry = entries[root];
        entries[root] = entries[child];
        entries[child] = entry;
        root = child;
    }
}

static void history_sort(Identity *entries, size_t count)
{
    for (size_t i = count / 2; i; --i) history_sift(entries, count, i - 1);
    for (size_t i = count; i > 1; --i) {
        Identity entry = entries[0];
        entries[0] = entries[i - 1];
        entries[i - 1] = entry;
        history_sift(entries, i - 1, 0);
    }
}

static Identity history_entry(const HolTermStore *s, int table, size_t index)
{
    if (table) return s->identities[index];
    TermNode node = NODE(s, s->base + index);
    return (Identity) { node.tag == HT_VAR || node.tag == HT_NOMINAL ? node.uid : UID_EMPTY, s->base + index };
}

static int history_changes_summaries(const HolTermStore *saved, const HolTermStore *live)
{
    if (saved->successor != live->successor) return 1;
    if (saved->mark_count == live->mark_count && (!saved->mark_count || !memcmp(saved->marks, live->marks, saved->mark_count))) return 0;
    /* An appended symbol normally cannot occur in the saved state. The term
        * API can construct a symbol before its role is known, so check it. */
    for (size_t i = saved->base; i < saved->count; ++i) {
        TermNode n = NODE(saved, i);
        if (n.tag != HT_CONST) continue;
        unsigned old = n.a < saved->mark_count ? saved->marks[n.a] : 0;
        unsigned now = n.a < live->mark_count ? live->marks[n.a] : 0;
        if ((old ^ now) & (MARK_OPAQUE | MARK_ARITHMETIC)) return 1;
    }
    return 0;
}

/* A consuming machine restore calls this only for stores from one query.
    * Retirement and the symbol vocabulary are monotone across its restores;
    * existing symbol roles never change, and every shared-prefix symbol is
    * below the saved vocabulary frontier. Thus only private summaries refresh.
    * Preflight may grow the retirement buffer, but no state changes on failure.
    * After it succeeds, live is destruction-only: its hash entries are used as
    * allocation-free sorting space and its owned metadata moves to restored. */
int ht_consume_history(HolTermStore *restored, HolTermStore *live)
{
    if (!restored || !live || restored == live || restored->memory != live->memory
        || restored->error[0] || restored->next_uid > live->next_uid) return 0;
    size_t at = 0;
    for (size_t i = 0; i < restored->retired_count; ++i) {
        RetiredRange range = restored->retired[i];
        while (at < live->retired_count && live->retired[at].end <= range.first) ++at;
        if (at == live->retired_count || live->retired[at].first > range.first || live->retired[at].end < range.end) return 0;
    }
    size_t private_count = live->count - live->base;
    int table = live->identity_capacity <= private_count;
    size_t limit = table ? live->identity_capacity : private_count;
    size_t missing = 0;
    for (size_t i = 0; i < limit; ++i) {
        uint64_t uid = history_entry(live, table, i).uid;
        if (uid != UID_EMPTY && ht_lookup_uid(restored, uid) == HT_NONE) ++missing;
    }
    if (missing > SIZE_MAX - live->retired_count || restored->identity_count > SIZE_MAX - live->retired_count - missing) return 0;
    size_t needed = live->retired_count + missing + restored->identity_count;
    if (needed > live->retired_capacity) {
        if (needed > SIZE_MAX / sizeof(*live->retired)) return 0;
        RetiredRange *ranges = hm_realloc(live->memory, live->retired, needed * sizeof(*ranges));
        if (!ranges) return 0;
        live->retired = ranges;
        live->retired_capacity = needed;
    }
    int refresh = history_changes_summaries(restored, live);
    if (refresh && !private_pages(restored)) return 0;
    /* From here, every operation is allocation-free and cannot fail. */
    size_t count = 0;
    for (size_t i = 0; i < limit; ++i) {
        Identity entry = history_entry(live, table, i);
        if (entry.uid != UID_EMPTY && ht_lookup_uid(restored, entry.uid) == HT_NONE) live->identities[count++] = entry;
    }
    history_sort(live->identities, count);
    retire_sorted_from(live, live->identities, count, sizeof(*live->identities));
    RetiredRange *old_ranges = restored->retired;
    restored->retired = live->retired;
    live->retired = old_ranges;
    restored->retired_count = live->retired_count;
    restored->retired_capacity = live->retired_capacity;
    restored->next_uid = live->next_uid;
    unsigned char *old_marks = restored->marks;
    restored->marks = live->marks;
    live->marks = old_marks;
    restored->mark_count = live->mark_count;
    restored->mark_capacity = live->mark_capacity;
    restored->successor = live->successor;
    restored->arrow = live->arrow;
    restored->work_limit = live->work_limit;
    memo_invalidate(restored);
    if (refresh) for (size_t i = restored->base; i < restored->count; ++i) summarize(restored, &NODE(restored, i));
    return 1;
}

void ht_set_arrow(HolTermStore *s, size_t symbol)
{
    if (s->arrow != symbol) {
        s->arrow = symbol;
        memo_invalidate(s);
    }
}

int ht_set_successor(HolTermStore *s, size_t symbol)
{
    if (!s || s->error[0]) return 0;
    if (s->successor == symbol) return 1;
    if (!prepare_summaries(s, 1)) return 0;
    s->successor = symbol;
    refresh_summaries(s);
    return 1;
}

static int mark_symbol(HolTermStore *s, size_t symbol, unsigned char mark, const char *invalid)
{
    if (!s || s->error[0] || symbol >= INT64_MAX || symbol == SIZE_MAX) {
        return fail(s, invalid);
    }
    if (marked(s, symbol, mark)) return 1;
    size_t count = symbol + 1;
    if (!reserve(s, s->marks, &s->mark_capacity, count, sizeof(*s->marks))) return 0;
    if (!prepare_summaries(s, s->prefix && symbol <= s->prefix->max_symbol)) return 0;
    if (count > s->mark_count) {
        memset(s->marks + s->mark_count, 0, count - s->mark_count);
        s->mark_count = count;
    }
    s->marks[symbol] |= mark;
    refresh_summaries(s);
    return 1;
}

int ht_set_opaque_symbol(HolTermStore *s, size_t symbol)
{
    return mark_symbol(s, symbol, MARK_OPAQUE, "Invalid opaque symbol");
}

int ht_set_arithmetic_symbol(HolTermStore *s, size_t symbol)
{
    return mark_symbol(s, symbol, MARK_ARITHMETIC, "Invalid arithmetic symbol");
}

/* No summary of a node depends on this mark. */
int ht_set_type_symbol(HolTermStore *s, size_t symbol)
{
    if (!s || s->error[0] || symbol >= INT64_MAX || symbol == SIZE_MAX) {
        return fail(s, "Invalid type symbol");
    }
    size_t count = symbol + 1;
    if (!reserve(s, s->marks, &s->mark_capacity, count, sizeof(*s->marks))) {
        return 0;
    }
    if (count > s->mark_count) {
        memset(s->marks + s->mark_count, 0, count - s->mark_count);
        s->mark_count = count;
    }
    s->marks[symbol] |= MARK_TYPE;
    return 1;
}

int ht_set_work_limit(HolTermStore *s, uint64_t visits)
{
    if (!s || !visits) {
        return fail(s, "The native term work limit must be positive");
    }
    s->work_limit = visits;
    return 1;
}

uint64_t ht_work_limit(const HolTermStore *s)
{
    return s ? s->work_limit : 0;
}

static int operation_begin(HolTermStore *s)
{
    if (!s || s->error[0]) {
        return 0;
    }
    if (!s->operations) {
        s->work = 0;
    }
    if (s->operations == SIZE_MAX) {
        return fail(s, "Native term operation nesting overflow");
    }
    ++s->operations;
    return 1;
}

static void operation_end(HolTermStore *s)
{
    --s->operations;
}

static HTerm identity_node(HolTermStore *s, int tag, uint64_t uid, size_t scope, int is_type, int64_t meta, int restoring)
{
    if (uid >= INT64_MAX || scope > INT64_MAX || (is_type != 0 && is_type != 1) || meta < -1) {
        fail(s, "Invalid term identity metadata");
        return HT_NONE;
    }
    HTerm result = node(s, (TermNode) { tag, is_type, 0, 0, 0, HT_NONE, HT_NONE, uid, scope, meta, NULL, 0, 0 });
    if (result == HT_NONE) return HT_NONE;
    if (!insert_identity(s, uid, result, restoring)) {
        /* An unpublished identity must not enter snapshot retirement. */
        --s->count;
        truncate_arena(&s->arena, s->count - s->base, 0);
        return HT_NONE;
    }
    if (s->next_uid <= uid) {
        s->next_uid = uid + 1;
    }
    return result;
}

HTerm ht_var(HolTermStore *s, size_t scope, int is_type, int64_t meta)
{
    return identity_node(s, HT_VAR, s->next_uid, scope, is_type, meta, 0);
}

HTerm ht_nominal(HolTermStore *s, size_t scope, int64_t meta)
{
    return identity_node(s, HT_NOMINAL, s->next_uid, scope, 0, meta, 0);
}

HTerm ht_var_typed(HolTermStore *s, size_t scope, int is_type, int64_t meta, HTerm type)
{
    if (type != HT_NONE && type >= s->count) { fail(s, "Invalid variable type"); return HT_NONE; }
    HTerm result = ht_var(s, scope, is_type, meta);
    if (result != HT_NONE) NODE(s, result).b = type;
    return result;
}

HTerm ht_nominal_typed(HolTermStore *s, size_t scope, int64_t meta, HTerm type)
{
    if (type != HT_NONE && type >= s->count) { fail(s, "Invalid nominal type"); return HT_NONE; }
    HTerm result = ht_nominal(s, scope, meta);
    if (result != HT_NONE) NODE(s, result).b = type;
    return result;
}

HTerm ht_type(const HolTermStore *s, HTerm term)
{
    if (term >= s->count) return HT_NONE;
    TermNode n = NODE(s, term);
    return n.tag == HT_VAR || n.tag == HT_NOMINAL || n.tag == HT_LAM ? n.b : HT_NONE;
}

HTerm ht_constant(HolTermStore *s, size_t symbol, int64_t meta)
{
    if (symbol > INT64_MAX || meta < -1) {
        fail(s, "Invalid constant metadata");
        return HT_NONE;
    }
    return node(s, (TermNode) { HT_CONST, 0, 0, 0, 0, symbol, HT_NONE, 0, 0, meta, NULL, 0, 0 });
}

HTerm ht_nat(HolTermStore *s, const char *digits)
{
    if (!digits || !*digits) {
        fail(s, "Invalid natural literal");
        return HT_NONE;
    }
    for (const char *p = digits; *p; ++p) {
        if (*p < '0' || *p > '9') {
            fail(s, "Invalid natural literal");
            return HT_NONE;
        }
    }
    while (digits[0] == '0' && digits[1]) {
        ++digits;
    }
    size_t length = strlen(digits);
    char *copy = hm_alloc(s->memory, length + 1);
    if (!copy) {
        fail(s, "Natural literal allocation failed");
        return HT_NONE;
    }
    memcpy(copy, digits, length + 1);
    HTerm result = node(s, (TermNode) { HT_NAT, 0, 0, 0, 0, HT_NONE, HT_NONE, 0, 0, -1, copy, 0, 0 });
    if (result == HT_NONE) {
        hm_free(copy);
    }
    return result;
}

static HTerm increment(HolTermStore *s, HTerm natural, int direction)
{
    const char *digits = NODE(s, natural).digits;
    size_t length = strlen(digits);
    char *work = hm_alloc(s->memory, length + 2);
    if (!work) {
        fail(s, "Natural arithmetic allocation failed");
        return HT_NONE;
    }
    memcpy(work + 1, digits, length + 1);
    size_t i = length;
    if (direction > 0) {
        while (i && work[i] == '9') {
            work[i--] = '0';
        }
        if (i) {
            ++work[i];
        } else {
            work[0] = '1';
        }
    } else {
        while (i && work[i] == '0') {
            work[i--] = '9';
        }
        if (!i) {
            hm_free(work);
            fail(s, "Natural predecessor of zero");
            return HT_NONE;
        }
        --work[i];
    }
    HTerm result = ht_nat(s, i ? work + 1 : work);
    hm_free(work);
    return result;
}

HTerm ht_index(HolTermStore *s, size_t index)
{
    if (index > INT64_MAX) {
        fail(s, "Bound variable index overflow");
        return HT_NONE;
    }
    return node(s, (TermNode) { HT_INDEX, 0, 0, 0, 0, index, HT_NONE, 0, 0, -1, NULL, 0, 0 });
}

HTerm ht_lam(HolTermStore *s, HTerm body, int64_t meta)
{
    return ht_lam_typed(s, body, meta, HT_NONE);
}

HTerm ht_lam_typed(HolTermStore *s, HTerm body, int64_t meta, HTerm type)
{
    if (body >= s->count || meta < -1 || (type != HT_NONE && type >= s->count)) {
        fail(s, "Invalid lambda term or type");
        return HT_NONE;
    }
    return node(s, (TermNode) { HT_LAM, 0, 0, 0, 0, body, type, 0, 0, meta, NULL, 0, 0 });
}

HTerm ht_app(HolTermStore *s, HTerm function, HTerm argument, int64_t meta)
{
    if (function >= s->count || argument >= s->count || meta < -1) {
        fail(s, "Invalid application term");
        return HT_NONE;
    }
    HTerm f = ht_deref(s, function);
    HTerm a = ht_deref(s, argument);
    if (NODE(s, f).tag == HT_CONST && NODE(s, f).a == s->successor && NODE(s, a).tag == HT_NAT) {
        return increment(s, a, 1);
    }
    return node(s, (TermNode) { HT_APP, 0, 0, 0, 0, function, argument, 0, 0, meta, NULL, 0, 0 });
}

HTerm ht_wildcard(HolTermStore *s)
{
    return node(s, (TermNode) { HT_WILD, 0, 0, 0, 0, HT_NONE, HT_NONE, 0, 0, -1, NULL, 0, 0 });
}

HTStringBuffer *ht_string_buffer(HolTermStore *s, size_t cons, size_t nil, size_t type, const int64_t *symbols, size_t count)
{
    if (!s || s->error[0]) {
        return NULL;
    }
    if (!symbols || !count || count > (SIZE_MAX - sizeof(HTStringBuffer)) / sizeof(StringChar) || cons > INT64_MAX || nil > INT64_MAX || type > INT64_MAX) {
        fail(s, "Invalid string buffer");
        return NULL;
    }
    HTStringBuffer *buffer = hm_alloc(s->memory, sizeof(*buffer) + count * sizeof(*buffer->chars));
    if (!buffer) {
        fail(s, "String buffer allocation failed");
        return NULL;
    }
    atomic_init(&buffer->references, 1);
    buffer->cons = cons;
    buffer->nil = nil;
    buffer->type = type;
    buffer->count = count;
    uint64_t hash = 0;
    for (size_t i = count; i > 0; --i) {
        int64_t symbol = symbols[i - 1];
        if (symbol < 0 || (uint64_t) symbol > SIZE_MAX) {
            hm_free(buffer);
            fail(s, "Invalid string buffer");
            return NULL;
        }
        hash = (uint64_t) symbol + 1 + UINT64_C(0x100000001b3) * hash;
        buffer->chars[i - 1] = (StringChar) { (size_t) symbol, hash };
    }
    return buffer;
}

/* Whether the node is literally function applied to argument, two constants. */
static int constant_pair(const HolTermStore *s, HTerm term, size_t function, size_t argument)
{
    TermNode n = NODE(s, term);
    if (n.tag != HT_APP) {
        return 0;
    }
    TermNode f = NODE(s, n.a), x = NODE(s, n.b);
    return f.tag == HT_CONST && f.a == function && x.tag == HT_CONST && x.a == argument;
}

/* The cell is checked against its buffer here, node by node and without a
    * dereference, so that what a cell says about itself holds for good. */
HTerm ht_string_cell(HolTermStore *s, HTerm function, HTerm tail, int64_t meta, HTStringBuffer *buffer, size_t offset)
{
    if (!s || s->error[0]) {
        return HT_NONE;
    }
    int valid = buffer && offset < buffer->count && function < s->count && tail < s->count && meta >= -1;
    if (valid) {
        TermNode f = NODE(s, function), t = NODE(s, tail);
        valid = f.tag == HT_APP && NODE(s, f.b).tag == HT_CONST && NODE(s, f.b).a == buffer->chars[offset].symbol && constant_pair(s, f.a, buffer->cons, buffer->type);
        if (valid && offset + 1 < buffer->count) {
            valid = t.tag == HT_APP && string_of(t) == buffer && t.uid == offset + 1;
        } else if (valid) {
            valid = constant_pair(s, tail, buffer->nil, buffer->type);
        }
    }
    if (!valid) {
        fail(s, "Invalid string cell");
        return HT_NONE;
    }
    atomic_fetch_add_explicit(&buffer->references, 1, memory_order_relaxed);
    HTerm result = node(s, (TermNode) { HT_APP, 0, 0, 0, 0, function, tail, offset, 0, meta, (char *) buffer, 0, 0 });
    if (result == HT_NONE) {
        ht_string_release(buffer);
    }
    return result;
}

HTerm ht_lookup_uid(const HolTermStore *s, uint64_t uid)
{
    if (!s->identity_capacity) {
        return HT_NONE;
    }
    size_t index = bucket(uid, s->identity_capacity);
    while (s->identities[index].uid != UID_EMPTY) {
        if (s->identities[index].uid == uid) {
            return s->identities[index].term;
        }
        index = (index + 1) & (s->identity_capacity - 1);
    }
    return HT_NONE;
}

HTerm ht_deref(const HolTermStore *s, HTerm term)
{
    if (!s || term >= s->count) {
        return HT_NONE;
    }
    /* Sealing stops before the first variable or nominal. A handle in the
        * shared prefix therefore needs no node lookup to dereference it.
        * Unsharing resets base; aliases into the prefix stop here too. */
    while (term >= s->base && NODE(s, term).tag == HT_VAR && NODE(s, term).a != HT_NONE) {
        term = NODE(s, term).a;
    }
    return term;
}

HTView ht_view(const HolTermStore *s, HTerm term)
{
    if (!s || term >= s->count) {
        return (HTView) { -1, HT_NONE, HT_NONE, 0, 0, 0, 0, -1, NULL };
    }
    TermNode n = NODE(s, term);
    return (HTView) { n.tag, n.a, n.b, n.uid, n.a, n.scope, n.is_type, n.meta, n.digits };
}

/* A parent whose rebuilt children are the dereferences of its own children is
    * returned as it is: every reader dereferences a child before inspecting it. */
static int unchanged(const HolTermStore *s, HTerm result, HTerm original)
{
    return result == original || (result != HT_NONE && result == ht_deref(s, original));
}

static int work_okay(HolTermStore *s)
{
    hm_count(s->memory, HM_VISITS, 1);
    if (s->work >= s->work_limit) {
        s->error_code = HT_ERROR_WORK;
        return fail(s, "Native term work limit exceeded");
    }
    ++s->work;
    return 1;
}

/* The traversals below keep their pending steps in s->frames instead of the C
    * stack, so that the depth of a term is bounded by memory alone. An operation
    * owns the frames above the count it found, and a nested operation stacks its
    * own on top. A frame is read by value: entering a term can move the array. */
static int enter(HolTermStore *s, HTerm term, size_t level, int form)
{
    if (term == HT_NONE || !reserve(s, s->frames, &s->frame_capacity, s->frame_count + 1, sizeof(*s->frames))) {
        return 0;
    }
    s->frames[s->frame_count++] = (Frame) { term, HT_NONE, level, 0, (unsigned char) form };
    return 1;
}

/* Rewritings of loose indices. level is the number of binders above
    * the node: an index below it is bound inside the term and stays. */
enum { MAP_SHIFT, MAP_SUBSTITUTE, MAP_INSTANTIATE, MAP_REMOVE, MAP_BETA };

typedef struct IndexMemo IndexMemo;

typedef struct {
    int kind;
    size_t amount;
    HTerm argument;
    const HTerm *values;
    size_t count;
    IndexMemo *bounds;
} IndexMap;

/* An index rewrite changes no binding. A result can therefore be shared for
    * the same dereferenced node and binder depth within this one rewrite.
    * Each nested shift has its own table; no entry survives an operation. */
typedef struct { HTerm key, result; size_t level; } IndexMemoEntry;
struct IndexMemo {
    IndexMemoEntry *entries;
    size_t count, capacity;
    IndexMemoEntry initial[32];
};

static size_t index_memo_slot(const IndexMemoEntry *entries, size_t capacity, HTerm key, size_t level)
{
    size_t slot = (size_t) ((uint64_t) key * UINT64_C(11400714819323198485) ^ (uint64_t) level * UINT64_C(14029467366897019727)) & (capacity - 1);
    while (entries[slot].key && (entries[slot].key != key || entries[slot].level != level)) slot = (slot + 1) & (capacity - 1);
    return slot;
}

static int index_memo_put(HolTermStore *s, IndexMemo *memo, HTerm term, size_t level, HTerm result)
{
    if (memo->count >= memo->capacity / 2) {
        if (memo->capacity > SIZE_MAX / 2 / sizeof(*memo->entries)) return fail(s, "Index rewrite memo size overflow");
        size_t capacity = memo->capacity * 2;
        IndexMemoEntry *entries = hm_calloc(s->memory, capacity, sizeof(*entries));
        if (!entries) return fail(s, "Out of memory while memoizing an index rewrite");
        for (size_t i = 0; i < memo->capacity; ++i) {
            IndexMemoEntry entry = memo->entries[i];
            if (entry.key) entries[index_memo_slot(entries, capacity, entry.key, entry.level)] = entry;
        }
        if (memo->entries != memo->initial) hm_free(memo->entries);
        memo->entries = entries;
        memo->capacity = capacity;
    }
    size_t slot = index_memo_slot(memo->entries, memo->capacity, term + 1, level);
    if (!memo->entries[slot].key) ++memo->count;
    memo->entries[slot] = (IndexMemoEntry) { term + 1, result, level };
    return 1;
}

/* Current-binding loose-index bounds. This table belongs to one normalization
    * and is discarded before any logical mutation can occur. */
static int index_bound(HolTermStore *s, IndexMemo *memo, HTerm root, size_t *output)
{
    size_t base = s->frame_count, result = 0;
    if (!enter(s, root, 0, 0)) return 0;
    while (s->frame_count > base) {
        Frame frame = s->frames[s->frame_count - 1];
        if (!frame.stage) {
            if (!work_okay(s)) break;
            HTerm term = ht_deref(s, frame.term);
            if (term == HT_NONE) { fail(s, "Invalid term reference"); break; }
            TermNode n = NODE(s, term);
            IndexMemoEntry cached = memo->entries[index_memo_slot(memo->entries, memo->capacity, term + 1, 0)];
            if (cached.key) result = cached.result;
            else if (stable(n) && n.open != OPEN_UNKNOWN) result = n.open;
            else if (n.tag == HT_INDEX) result = n.a == SIZE_MAX ? SIZE_MAX : n.a + 1;
            else if (n.tag != HT_APP && n.tag != HT_LAM) result = 0;
            else {
                s->frames[s->frame_count - 1].term = term;
                s->frames[s->frame_count - 1].stage = 1;
                if (!enter(s, n.a, 0, 0)) break;
                continue;
            }
            if (!cached.key && !index_memo_put(s, memo, term, 0, result)) break;
        } else {
            TermNode n = NODE(s, frame.term);
            if (frame.stage == 1) {
                if (n.tag == HT_LAM && result && result != SIZE_MAX) --result;
                if (n.b != HT_NONE) {
                    s->frames[s->frame_count - 1].left = result;
                    s->frames[s->frame_count - 1].stage = 2;
                    if (!enter(s, n.b, 0, 0)) break;
                    continue;
                }
            } else if (frame.left > result) result = frame.left;
            if (!index_memo_put(s, memo, frame.term, 0, result)) break;
        }
        --s->frame_count;
    }
    if (s->frame_count > base) { s->frame_count = base; return 0; }
    *output = result;
    return 1;
}

static HTerm map_indices(HolTermStore *s, HTerm root, size_t level, const IndexMap *map);

static HTerm shift(HolTermStore *s, HTerm term, size_t amount, size_t cutoff)
{
    IndexMap map = { MAP_SHIFT, amount, HT_NONE, NULL, 0, NULL };
    if (!amount) {
        return term != HT_NONE && work_okay(s) ? ht_deref(s, term) : HT_NONE;
    }
    return map_indices(s, term, cutoff, &map);
}

static HTerm map_index(HolTermStore *s, HTerm term, size_t index, size_t level, const IndexMap *map)
{
    switch (map->kind) {
        case MAP_SHIFT:
            if (index < level) {
                return term;
            }
            if (index > INT64_MAX - map->amount) {
                fail(s, "Bound variable shift overflow");
                return HT_NONE;
            }
            return ht_index(s, index + map->amount);
        case MAP_SUBSTITUTE:
            if (index == level) {
                return shift(s, map->argument, level, 0);
            }
            return index > level ? ht_index(s, index - 1) : term;
        case MAP_INSTANTIATE:
            if (index < level) {
                return term;
            }
            return index - level < map->count ? map->values[map->count - 1 - (index - level)] : ht_index(s, index - map->count);
        case MAP_BETA:
            if (index < level) return term;
            if (index - level >= map->count) return ht_index(s, index - map->count);
            HTerm replacement = ht_deref(s, map->values[map->count - 1 - (index - level)]);
            if (replacement == HT_NONE) {
                fail(s, "Invalid term reference");
                return HT_NONE;
            }
            if (!level) return replacement;
            if (NODE(s, replacement).tag == HT_INDEX) {
                size_t original = NODE(s, replacement).a;
                if (level > INT64_MAX || original > (size_t) INT64_MAX - level) {
                    fail(s, "Bound variable shift overflow");
                    return HT_NONE;
                }
                return original + level == index ? term : ht_index(s, original + level);
            }
            return shift(s, replacement, level, 0);
        default:
            return index > level ? ht_index(s, index - 1) : term;
    }
}

/* The structural bound follows the same edges as an index rewrite: both
    * children of an application, a lambda body and its annotation, and no
    * children of a variable or nominal. Substituting closed terms for these
    * variables preserves the bound. If any binding ever installs an open (or
    * unknown) value, rely on immutable nodes or the current-binding table. */
static size_t rewrite_bound(const HolTermStore *s, TermNode n)
{
    return (!s->binding_has_loose_indices || stable(n)) && n.open != OPEN_UNKNOWN ? n.open : SIZE_MAX;
}

/* Stages of a frame: 0 not visited yet; 1 an application whose function is
    * being rewritten; 2 its argument; 3 an abstraction whose body is. */
static HTerm map_indices(HolTermStore *s, HTerm root, size_t level, const IndexMap *map)
{
    size_t base = s->frame_count;
    HTerm result = HT_NONE;
    HTerm resolved = ht_deref(s, root);
    if (resolved == HT_NONE) { fail(s, "Invalid term reference"); return HT_NONE; }
    size_t root_bound = rewrite_bound(s, NODE(s, resolved));
    if (root_bound != SIZE_MAX && root_bound <= level + (map->kind == MAP_REMOVE)) {
        return work_okay(s) ? resolved : HT_NONE;
    }
    if (!enter(s, root, level, 0)) {
        return HT_NONE;
    }
    IndexMemo memo = { 0 };
    memo.entries = memo.initial;
    memo.capacity = sizeof(memo.initial) / sizeof(*memo.initial);
    while (s->frame_count > base) {
        Frame frame = s->frames[s->frame_count - 1];
        if (frame.stage == 0) {
            if (!work_okay(s)) {
                break;
            }
            HTerm term = ht_deref(s, frame.term);
            if (term == HT_NONE) { fail(s, "Invalid term reference"); break; }
            TermNode n = NODE(s, term);
            size_t bound = rewrite_bound(s, n);
            if (bound == SIZE_MAX && map->bounds && !index_bound(s, map->bounds, term, &bound)) break;
            if (bound != SIZE_MAX && bound <= frame.level + (map->kind == MAP_REMOVE)) {
                result = term;
            } else if (n.tag == HT_INDEX) {
                result = map_index(s, term, n.a, frame.level, map);
            } else if (n.tag == HT_APP || n.tag == HT_LAM) {
                IndexMemoEntry cached = memo.entries[index_memo_slot(memo.entries, memo.capacity, term + 1, frame.level)];
                if (cached.key) {
                    result = cached.result;
                    --s->frame_count;
                    continue;
                }
                s->frames[s->frame_count - 1].term = term;
                int typed = n.tag == HT_LAM && n.b != HT_NONE;
                s->frames[s->frame_count - 1].stage = n.tag == HT_APP ? 1 : typed ? 4 : 3;
                if (!enter(s, typed ? n.b : n.a, frame.level + (n.tag == HT_LAM && !typed), 0)) {
                    break;
                }
                continue;
            } else {
                result = term;
            }
        } else if (frame.stage == 4) {
            s->frames[s->frame_count - 1].left = result;
            s->frames[s->frame_count - 1].stage = 3;
            if (!enter(s, NODE(s, frame.term).a, frame.level + 1, 0)) {
                break;
            }
            continue;
        } else if (frame.stage == 1) {
            s->frames[s->frame_count - 1].left = result;
            s->frames[s->frame_count - 1].stage = 2;
            if (!enter(s, NODE(s, frame.term).b, frame.level, 0)) {
                break;
            }
            continue;
        } else {
            TermNode n = NODE(s, frame.term);
            if (frame.stage == 2) {
                result = unchanged(s, frame.left, n.a) && unchanged(s, result, n.b) ? frame.term : ht_app(s, frame.left, result, n.meta);
            } else {
                result = unchanged(s, result, n.a) && frame.left == n.b ? frame.term : ht_lam_typed(s, result, n.meta, frame.left);
            }
            if (result != HT_NONE && !index_memo_put(s, &memo, frame.term, frame.level, result)) result = HT_NONE;
        }
        if (result == HT_NONE) {
            break;
        }
        --s->frame_count;
    }
    if (memo.entries != memo.initial) hm_free(memo.entries);
    if (s->frame_count > base) {
        s->frame_count = base;
        return HT_NONE;
    }
    return result;
}

static HTerm substitute(HolTermStore *s, HTerm term, HTerm argument, size_t binder)
{
    IndexMap map = { MAP_SUBSTITUTE, 0, argument, NULL, 0, NULL };
    return argument == HT_NONE ? HT_NONE : map_indices(s, term, binder, &map);
}

/* Index i of the body of count nested binders denotes values[count - 1 - i]. */
static HTerm instantiate(HolTermStore *s, HTerm term, const HTerm *values, size_t count, size_t binders)
{
    IndexMap map = { MAP_INSTANTIATE, 0, HT_NONE, values, count, NULL };
    return map_indices(s, term, binders, &map);
}

static HTerm remove_binder(HolTermStore *s, HTerm term, size_t index)
{
    IndexMap map = { MAP_REMOVE, 0, HT_NONE, NULL, 0, NULL };
    return map_indices(s, term, index, &map);
}

HTerm ht_instantiate(HolTermStore *s, HTerm body, const HTerm *values, size_t count)
{
    if (!operation_begin(s)) {
        return HT_NONE;
    }
    HTerm result = HT_NONE;
    int closed = body < s->count && (values || !count);
    for (size_t i = 0; closed && i < count; ++i) {
        closed = values[i] < s->count && (NODE(s, values[i]).tag == HT_VAR || NODE(s, values[i]).tag == HT_NOMINAL);
    }
    if (closed) {
        result = instantiate(s, body, values, count, 0);
    } else {
        fail(s, "Invalid simultaneous instantiation");
    }
    operation_end(s);
    return result;
}

/* Open constructor summaries are valid until one of their dependent variables
    * changes. A Fenwick tree records the newest mutation below a handle; fresh
    * clause variables above that bound do not invalidate the old term. The
    * summaries also include type edges, so direct binding cannot hide a scope
    * or occurrence dependency there. Only private nodes have cache entries. */
static void memo_invalidate(HolTermStore *s)
{
    if (++s->memo_generation == 0) {
        if (s->memo_valid) memset(s->memo_valid, 0, s->memo_valid_capacity * sizeof(*s->memo_valid));
        s->memo_generation = 1;
    }
}

static void memo_release(HolTermStore *s)
{
    hm_free(s->memo);
    hm_free(s->memo_valid);
    hm_free(s->memo_changes);
    hm_free(s->memo_frames);
    s->memo = NULL;
    s->memo_valid = NULL;
    s->memo_valid_capacity = 0;
    s->memo_changes = NULL;
    s->memo_frames = NULL;
    s->memo_capacity = s->memo_change_capacity = s->memo_frame_capacity = 0;
    s->memo_base = s->base;
    memo_invalidate(s);
}

static void memo_rebase(HolTermStore *s)
{
    if (s->memo_base != s->base) memo_release(s);
}
static uint64_t memo_changed(const HolTermStore *s, size_t n)
{
    uint64_t serial = 0;
    n = n > s->base ? n - s->base : 0;
    while (n) {
        if (s->memo_changes[n - 1] > serial) serial = s->memo_changes[n - 1];
        n &= n - 1;
    }
    return serial;
}

static void memo_mutated(HolTermStore *s, size_t variable)
{
    memo_rebase(s);
    if (++s->memo_serial == 0) {
        memo_invalidate(s);
        s->memo_serial = 1;
        if (s->memo_changes) memset(s->memo_changes, 0, s->memo_change_capacity * sizeof(*s->memo_changes));
    }
    if (variable < s->base) { memo_invalidate(s); return; }
    for (size_t i = variable - s->base + 1; i && i <= s->memo_change_capacity; i += i & (~i + 1)) {
        s->memo_changes[i - 1] = s->memo_serial;
    }
}

static int memo_reserve(HolTermStore *s)
{
    memo_rebase(s);
    if (!reserve(s, s->memo, &s->memo_capacity, s->count - s->base, sizeof(*s->memo))) return 0;
    size_t old = s->memo_valid_capacity;
    size_t words = s->memo_capacity / 64 + (s->memo_capacity % 64 != 0);
    if (!reserve(s, s->memo_valid, &s->memo_valid_capacity, words, sizeof(*s->memo_valid))) return 0;
    if (old < s->memo_valid_capacity) memset(s->memo_valid + old, 0, (s->memo_valid_capacity - old) * sizeof(*s->memo_valid));
    old = s->memo_change_capacity;
    if (!reserve(s, s->memo_changes, &s->memo_change_capacity, s->count - s->base, sizeof(*s->memo_changes))) return 0;
    if (old != s->memo_change_capacity) {
        memset(s->memo_changes + old, 0, (s->memo_change_capacity - old) * sizeof(*s->memo_changes));
        if (old) for (size_t i = old * 2; i <= s->memo_change_capacity; i *= 2) {
            s->memo_changes[i - 1] = s->memo_changes[old - 1];
            if (i > SIZE_MAX / 2) break;
        }
    }
    return 1;
}

/* The entries can be large. Initializing only one validity bit per
    * slot avoids writing the whole term heap on a cache miss after GC. */
static int memo_valid(const HolTermStore *s, HTerm term)
{
    if (term < s->base) return 0;
    size_t offset = term - s->base;
    return offset / 64 < s->memo_valid_capacity && (s->memo_valid[offset / 64] & (UINT64_C(1) << (offset % 64)));
}

static void memo_store(HolTermStore *s, HTerm term, OpenMemo entry)
{
    if (term < s->base) return;
    size_t offset = term - s->base;
    s->memo[offset] = entry;
    s->memo_valid[offset / 64] |= UINT64_C(1) << (offset % 64);
}

static OpenMemo memo_merge(OpenMemo a, OpenMemo b)
{
    if (b.variables > a.variables) a.variables = b.variables;
    if (b.scope > a.scope) a.scope = b.scope;
    a.exact = a.exact && b.exact;
    a.value_types = a.value_types || b.value_types;
    a.simple = a.simple && b.simple;
    return a;
}

/* Cache structural failures on their dependent ancestors, never errors. */
static int memo_failed(HolTermStore *s, HTerm term, size_t count, OpenMemo result)
{
    for (;;) {
        result.serial = s->memo_serial;
        result.generation = s->memo_generation;
        result.possible = 0;
        memo_store(s, term, result);
        if (!count) return 0;
        MemoFrame frame = s->memo_frames[--count];
        result = memo_merge(frame.left, result);
        term = frame.term;
    }
}

static HTerm arrow_result(HolTermStore *s, HTerm type, HTerm *domain);

static int open_memo(HolTermStore *s, HTerm root, OpenMemo *output)
{
    if (root == HT_NONE || root >= s->count) return 0;
    /* A scoped wire must not allocate a cache for unrelated private nodes.
        * Reuse only an existing valid positive certificate; a miss falls back
        * to normalization of the requested term without populating the cache. */
    if (s->transient_wire) {
        if (s->memo_base != s->base || root < s->base || root - s->base >= s->memo_capacity || !memo_valid(s, root)) return 0;
        OpenMemo cached = s->memo[root - s->base];
        if (!cached.possible || cached.generation != s->memo_generation
            || (cached.variables > s->base && cached.variables - s->base > s->memo_change_capacity)
            || memo_changed(s, cached.variables) > cached.serial) return 0;
        hm_count(s->memory, HM_NORMALIZE_VISITS, 1);
        if (!work_okay(s)) return 0;
        *output = cached;
        return 1;
    }
    if (!memo_reserve(s)) return 0;
    size_t count = 0;
    HTerm term = root;
    OpenMemo result = { 0 };
    int descend = 1;
    for (;;) {
        if (descend) {
            hm_count(s->memory, HM_NORMALIZE_VISITS, 1);
            if (!work_okay(s)) return 0;
            OpenMemo cached = memo_valid(s, term) ? s->memo[term - s->base] : (OpenMemo) { 0 };
            if (cached.generation == s->memo_generation && memo_changed(s, cached.variables) <= cached.serial) {
                if (!cached.possible) return memo_failed(s, term, count, cached);
                result = cached;
                descend = 0;
                continue;
            }
            TermNode n = NODE(s, term);
            result = (OpenMemo) { s->memo_serial, s->memo_generation, 0, 0, 0, 1, 0, 1, 0, 1, HT_NONE, UINT64_MAX, HT_NONE };
            if (n.ground && (n.summary & HS_NORMAL) == HS_NORMAL && !n.open) {
                result.scope = n.scope;
                result.rigid = n.tag == HT_NOMINAL || n.tag == HT_APP || (n.tag == HT_CONST && n.a != s->successor);
                result.callable = result.rigid;
            } else if (n.tag == HT_CONST) {
                if (n.a == s->successor || marked(s, n.a, MARK_OPAQUE)) return memo_failed(s, term, count, result);
                result.rigid = 1;
                result.callable = 1;
            } else if (n.tag == HT_NAT) {
                /* Natural literals cannot stand in function position. */
            } else if (n.tag == HT_NOMINAL) {
                result.rigid = 1;
                result.callable = 1;
                result.scope = n.scope;
                if (n.b != HT_NONE) {
                    if (!reserve(s, s->memo_frames, &s->memo_frame_capacity, count + 1, sizeof(*s->memo_frames))) return 0;
                    s->memo_frames[count++] = (MemoFrame) { term, 3, result };
                    term = n.b;
                    continue;
                }
            } else if (n.tag == HT_VAR) {
                if (n.b == HT_NONE && !n.is_type && n.a != HT_NONE) return memo_failed(s, term, count, (OpenMemo) { s->memo_serial, s->memo_generation, term + 1, n.scope, 0, 0, 0, 0, 0, 0, HT_NONE, UINT64_MAX, HT_NONE });
                result.variables = term + 1;
                result.scope = n.scope;
                result.exact = n.b != HT_NONE;
                result.value_types = n.is_type != 0;
                if ((n.pinned & 4) && n.a == HT_NONE) result.simple = 0;
                result.callable = 1;
                result.head_variable = term;
                result.flex_type = n.b;
                if (n.a != HT_NONE || n.b != HT_NONE) {
                    if (!reserve(s, s->memo_frames, &s->memo_frame_capacity, count + 1, sizeof(*s->memo_frames))) return 0;
                    s->memo_frames[count++] = (MemoFrame) { term, n.a != HT_NONE ? 2 : 3, result };
                    term = n.a != HT_NONE ? n.a : n.b;
                    continue;
                }
            } else if (n.tag == HT_INDEX) {
                result.callable = 1;
                result.simple = 0;
            } else if (n.tag == HT_LAM) {
                result.simple = 0;
                if (!reserve(s, s->memo_frames, &s->memo_frame_capacity, count + 1, sizeof(*s->memo_frames))) return 0;
                s->memo_frames[count++] = (MemoFrame) { term, 4, result };
                term = n.a;
                continue;
            } else if (n.tag == HT_APP) {
                if (!reserve(s, s->memo_frames, &s->memo_frame_capacity, count + 1, sizeof(*s->memo_frames))) return 0;
                s->memo_frames[count++] = (MemoFrame) { term, 0, result };
                term = n.a;
                continue;
            } else return memo_failed(s, term, count, result);
            memo_store(s, term, result);
            descend = 0;
        } else if (!count) {
            *output = result;
            return 1;
        } else {
            MemoFrame frame = s->memo_frames[count - 1];
            TermNode n = NODE(s, frame.term);
            if (frame.stage == 0) {
                if (!result.callable) return memo_failed(s, frame.term, count - 1, memo_merge(frame.left, result));
                s->memo_frames[count - 1].stage = 1;
                s->memo_frames[count - 1].left = result;
                term = n.b;
                descend = 1;
                continue;
            }
            int value_types = frame.left.value_types;
            int simple = frame.left.simple;
            int callable = frame.stage == 2 ? result.callable : frame.left.callable;
            HTerm head_variable = frame.stage == 2 ? result.head_variable : frame.left.head_variable;
            uint64_t last_nominal = frame.stage == 2 ? result.last_nominal : frame.left.last_nominal;
            HTerm flex_type = frame.stage == 2 ? result.flex_type : frame.left.flex_type;
            if (frame.stage == 1 && head_variable != HT_NONE) {
                HTerm argument_term = ht_deref(s, n.b);
                if (argument_term == HT_NONE) return fail(s, "Invalid term reference");
                TermNode argument = NODE(s, argument_term);
                /* Strict UID order is a sufficient distinctness proof. */
                int pattern_argument = argument.tag == HT_NOMINAL && argument.scope > NODE(s, head_variable).scope
                    && (last_nominal == UINT64_MAX || argument.uid > last_nominal);
                if (NODE(s, head_variable).b != HT_NONE) {
                    HTerm domain = HT_NONE;
                    flex_type = arrow_result(s, flex_type, &domain);
                    if (flex_type == HT_NONE) pattern_argument = 0;
                }
                if (!pattern_argument) result.simple = 0;
                else last_nominal = argument.uid;
            }
            int rigid = frame.stage == 2 ? result.rigid : frame.left.rigid;
            result = memo_merge(frame.left, result);
            result.rigid = rigid;
            result.callable = callable;
            result.head_variable = head_variable;
            result.last_nominal = last_nominal;
            result.flex_type = flex_type;
            if (frame.stage == 3) {
                result.value_types = value_types;
                result.simple = simple;
            }
            if ((frame.stage == 2 || frame.stage == 4) && n.b != HT_NONE) {
                s->memo_frames[count - 1].stage = 3;
                s->memo_frames[count - 1].left = result;
                term = n.b;
                descend = 1;
                continue;
            }
            result.serial = s->memo_serial;
            result.generation = s->memo_generation;
            memo_store(s, frame.term, result);
            --count;
        }
    }
}

/* Stages of a frame: 0 not visited yet; 1 an application whose function is
    * being brought to weak head normal form; 2 the same function in the form
    * asked for; 3 its argument; 4 an abstraction whose body is being normalized.
    * A beta step visits the same frame again with the contracted term. */
static HTerm normalize(HolTermStore *s, HTerm root, enum HTNormalForm form)
{
    size_t base = s->frame_count;
    HTerm result = HT_NONE;
    if (s->error[0] || root == HT_NONE) {
        return HT_NONE;
    }
    root = ht_deref(s, root);
    if (root == HT_NONE) {
        fail(s, "Invalid term reference");
        return HT_NONE;
    }
    TermNode entry = NODE(s, root);
    if ((entry.tag != HT_APP && entry.tag != HT_LAM)
        || ((form == HT_HNF || form == HT_WHNF) && (entry.summary & HS_RIGID_HEAD))
        || (entry.summary & (HS_STABLE | HS_BETA)) == (HS_STABLE | HS_BETA)) {
        return work_okay(s) ? root : HT_NONE;
    }
    OpenMemo memo;
    if ((form == HT_NF || (int) form == FORM_SPINE) && open_memo(s, root, &memo)) return work_okay(s) ? root : HT_NONE;
    if (s->error[0]) return HT_NONE;
    if (!enter(s, root, 0, form)) {
        return HT_NONE;
    }
    IndexMemo bounds = { 0 };
    bounds.entries = bounds.initial;
    bounds.capacity = sizeof(bounds.initial) / sizeof(*bounds.initial);
    while (s->frame_count > base) {
        Frame frame = s->frames[s->frame_count - 1];
        if (frame.stage == 0) {
            hm_count(s->memory, HM_NORMALIZE_VISITS, 1);
            if (!work_okay(s)) {
                break;
            }
            HTerm term = ht_deref(s, frame.term);
            if (term == HT_NONE) {
                fail(s, "Invalid term reference");
                break;
            }
            TermNode n = NODE(s, term);
            int settled = (n.summary & (HS_STABLE | HS_BETA)) == (HS_STABLE | HS_BETA);
            if (!settled && (frame.form == HT_NF || frame.form == FORM_SPINE) && open_memo(s, term, &memo)) {
                result = term;
                --s->frame_count;
                continue;
            }
            if (s->error[0]) break;
            if (!settled && n.tag == HT_APP) {
                /* An application on a weak-head normal spine has no redex at
                    * its head: its function part is on the same spine. */
                int spine = frame.form == FORM_SPINE;
                s->frames[s->frame_count - 1] = (Frame) { term, HT_NONE, 0, spine ? 2 : 1, (unsigned char) (spine ? HT_NF : frame.form) };
                if (!enter(s, n.a, 0, spine ? FORM_SPINE : HT_WHNF)) {
                    break;
                }
                continue;
            }
            if (!settled && n.tag == HT_LAM && frame.form != HT_WHNF) {
                int form = frame.form == FORM_SPINE ? HT_NF : frame.form;
                s->frames[s->frame_count - 1] = (Frame) { term, HT_NONE, 0, 4, (unsigned char) form };
                if (!enter(s, n.a, 0, form)) {
                    break;
                }
                continue;
            }
            result = term;
        } else if (frame.stage == 4) {
            TermNode n = NODE(s, frame.term);
            result = unchanged(s, result, n.a) ? frame.term : ht_lam_typed(s, result, n.meta, n.b);
        } else {
            TermNode n = NODE(s, frame.term);
            HTerm function = frame.stage == 3 ? frame.left : result;
            HTerm argument = frame.stage == 3 ? result : n.b;
            if (frame.stage == 1 && NODE(s, function).tag == HT_LAM) {
                /* Adjacent pending function frames are one application
                    * spine. Consume consecutive lambdas in one substitution,
                    * preserving the requested form of the outermost frame. */
                size_t consumed = 1;
                HTerm body = ht_deref(s, NODE(s, function).a);
                while (body != HT_NONE && NODE(s, body).tag == HT_LAM && consumed < s->frame_count - base) {
                    Frame parent = s->frames[s->frame_count - consumed - 1];
                    if (parent.stage != 1 || NODE(s, parent.term).tag != HT_APP) break;
                    if (!work_okay(s)) break;
                    ++consumed;
                    body = ht_deref(s, NODE(s, body).a);
                }
                if (s->error[0]) break;
                if (consumed > 1) {
                    HTerm few[8], *arguments = few;
                    if (consumed > sizeof(few) / sizeof(*few)) {
                        arguments = consumed <= SIZE_MAX / sizeof(*arguments) ? hm_alloc(s->memory, consumed * sizeof(*arguments)) : NULL;
                        if (!arguments) { fail(s, "Out of memory while contracting a beta spine"); break; }
                    }
                    for (size_t i = 0; i < consumed; ++i) arguments[i] = NODE(s, s->frames[s->frame_count - i - 1].term).b;
                    IndexMap map = { MAP_BETA, 0, HT_NONE, arguments, consumed, &bounds };
                    HTerm result_body = map_indices(s, body, 0, &map);
                    if (arguments != few) hm_free(arguments);
                    if (result_body == HT_NONE) break;
                    s->frame_count -= consumed - 1;
                    s->frames[s->frame_count - 1].term = result_body;
                    s->frames[s->frame_count - 1].stage = 0;
                    continue;
                }
                body = substitute(s, NODE(s, function).a, n.b, 0);
                if (body == HT_NONE) {
                    break;
                }
                s->frames[s->frame_count - 1].term = body;
                s->frames[s->frame_count - 1].stage = 0;
                continue;
            }
            /* The function part is weak-head normal and no abstraction, so
                * it is head normal as well. Its full normal form has the
                * arguments along its spine normalized, and nothing else. */
            if (frame.stage == 1 && frame.form == HT_NF) {
                s->frames[s->frame_count - 1].stage = 2;
                if (!enter(s, function, 0, FORM_SPINE)) {
                    break;
                }
                continue;
            }
            if (frame.stage != 3 && frame.form == HT_NF) {
                s->frames[s->frame_count - 1].left = function;
                s->frames[s->frame_count - 1].stage = 3;
                if (!enter(s, n.b, 0, HT_NF)) {
                    break;
                }
                continue;
            }
            int same = unchanged(s, function, n.a) && unchanged(s, argument, n.b);
            if (same) {
                HTerm arg = ht_deref(s, argument);
                same = arg == HT_NONE || NODE(s, function).tag != HT_CONST || NODE(s, function).a != s->successor || NODE(s, arg).tag != HT_NAT;
            }
            result = same ? frame.term : ht_app(s, function, argument, n.meta);
        }
        if (result == HT_NONE) {
            break;
        }
        --s->frame_count;
    }
    if (bounds.entries != bounds.initial) hm_free(bounds.entries);
    if (s->frame_count > base) {
        s->frame_count = base;
        return HT_NONE;
    }
    return result;
}

HTerm ht_normalize(HolTermStore *s, HTerm term, enum HTNormalForm form)
{
    if (!operation_begin(s)) {
        return HT_NONE;
    }
    HTerm result = normalize(s, term, form);
    operation_end(s);
    return result;
}

HTerm ht_apply(HolTermStore *s, HTerm function, HTerm argument)
{
    return ht_normalize(s, ht_app(s, function, argument, -1), HT_HNF);
}

static int mentions_arithmetic(HolTermStore *s, HTerm term)
{
    size_t base = s->frame_count;
    int found = 0;
    for (;;) {
        if (!work_okay(s)) {
            found = 1;
            break;
        }
        term = ht_deref(s, term);
        TermNode n = NODE(s, term);
        if (!stable(n) && n.tag == HT_APP) {
            if (!enter(s, n.b, 0, 0)) {
                found = 1;
                break;
            }
            term = n.a;
            continue;
        }
        if (!stable(n) && n.tag == HT_LAM) {
            term = n.a;
            continue;
        }
        found = stable(n) ? (n.summary & HS_ARITHMETIC) != 0 : n.tag == HT_CONST;
        if (found || s->frame_count == base) {
            break;
        }
        term = s->frames[--s->frame_count].term;
    }
    s->frame_count = base;
    return found;
}

int ht_mentions_arithmetic(HolTermStore *s, HTerm term)
{
    if (!operation_begin(s)) {
        return -1;
    }
    int result = -1;
    if (term >= s->count) {
        fail(s, "Invalid term reference");
    } else {
        result = mentions_arithmetic(s, term);
    }
    operation_end(s);
    return s->error[0] ? -1 : result;
}

static int spine_view(HolTermStore *s, HTerm term, HTSpine *spine)
{
    *spine = (HTSpine) { HT_NONE, NULL, 0, { 0 } };
    HTerm top = ht_deref(s, term), head = top;
    size_t count = 0;
    while (head != HT_NONE && NODE(s, head).tag == HT_APP) {
        if (!work_okay(s)) {
            return 0;
        }
        ++count;
        head = ht_deref(s, NODE(s, head).a);
    }
    if (head == HT_NONE) {
        return fail(s, "Invalid term spine");
    }
    HTerm predecessor = HT_NONE;
    if (NODE(s, head).tag == HT_NAT && strcmp(NODE(s, head).digits, "0")) {
        if (s->successor == HT_NONE) {
            return fail(s, "Natural successor symbol is not configured");
        }
        predecessor = increment(s, head, -1);
        head = ht_constant(s, s->successor, -1);
        if (predecessor == HT_NONE || head == HT_NONE) {
            return 0;
        }
        ++count;
    }
    HTerm *arguments = spine->few;
    if (count > sizeof(spine->few) / sizeof(*spine->few)) {
        arguments = count <= SIZE_MAX / sizeof(*arguments) ? hm_alloc(s->memory, count * sizeof(*arguments)) : NULL;
        if (!arguments) {
            return fail(s, "Term allocation failed");
        }
    }
    size_t at = count;
    for (HTerm node = top; NODE(s, node).tag == HT_APP; node = ht_deref(s, NODE(s, node).a)) {
        arguments[--at] = NODE(s, node).b;
    }
    if (predecessor != HT_NONE) {
        arguments[--at] = predecessor;
    }
    spine->head = head;
    spine->args = arguments;
    spine->count = count;
    return 1;
}

int ht_spine(HolTermStore *s, HTerm term, HTSpine *spine)
{
    *spine = (HTSpine) { HT_NONE, NULL, 0, { 0 } };
    if (!operation_begin(s)) {
        return 0;
    }
    int result = spine_view(s, term, spine);
    operation_end(s);
    return result;
}

void ht_spine_free(HTSpine *spine)
{
    if (spine->args != spine->few) {
        hm_free(spine->args);
    }
    *spine = (HTSpine) { HT_NONE, NULL, 0, { 0 } };
}

/* Two string cells are equal when they have the same elements from their
    * offsets on, between the same constructors. A different hash settles it. */
static int strings_equal(HolTermStore *s, const HTStringBuffer *x, size_t i, const HTStringBuffer *y, size_t j)
{
    if (x == y) {
        return i == j;
    }
    size_t length = x->count - i;
    if (length != y->count - j || x->chars[i].hash != y->chars[j].hash || x->cons != y->cons || x->nil != y->nil || x->type != y->type) {
        return 0;
    }
    for (size_t k = 0; k < length; ++k) {
        if (!work_okay(s) || x->chars[i + k].symbol != y->chars[j + k].symbol) {
            return 0;
        }
    }
    return 1;
}

static int constant_node(const HolTermStore *s, HTerm term, size_t symbol)
{
    TermNode n = NODE(s, ht_deref(s, term));
    return n.tag == HT_CONST && n.a == symbol;
}

/* A string cell against a list that is no such cell: what comparing the two
    * node by node says, with the cell's side read from its buffer. */
static int string_equal(HolTermStore *s, const HTStringBuffer *x, size_t at, HTerm right)
{
    HTerm constructor = HT_NONE;
    for (;;) {
        if (!work_okay(s)) {
            return 0;
        }
        right = ht_deref(s, right);
        TermNode cell = NODE(s, right);
        if (cell.tag != HT_APP) {
            return 0;
        }
        if (at == x->count) {
            return constant_node(s, cell.a, x->nil) && constant_node(s, cell.b, x->type);
        }
        if (cell.digits) {
            return strings_equal(s, x, at, string_of(cell), (size_t) cell.uid);
        }
        TermNode function = NODE(s, ht_deref(s, cell.a));
        if (function.tag != HT_APP || !constant_node(s, function.b, x->chars[at].symbol)) {
            return 0;
        }
        HTerm head = ht_deref(s, function.a);
        if (head != constructor) {
            TermNode typed = NODE(s, head);
            if (typed.tag != HT_APP || !constant_node(s, typed.a, x->cons) || !constant_node(s, typed.b, x->type)) {
                return 0;
            }
            constructor = head;
        }
        ++at;
        right = cell.b;
    }
}

/* The function parts are compared before the arguments, which wait in frames. */
static int equal(HolTermStore *s, HTerm left, HTerm right)
{
    size_t base = s->frame_count;
    int same = 1;
    while (same) {
        if (!work_okay(s)) {
            same = 0;
            break;
        }
        left = ht_deref(s, left);
        right = ht_deref(s, right);
        if (left == HT_NONE || right == HT_NONE) {
            fail(s, "Invalid term reference");
            same = 0;
            break;
        }
        if (left != right) {
            TermNode a = NODE(s, left), b = NODE(s, right);
            if (a.tag != b.tag || (stable(a) && stable(b) && (a.scope != b.scope || a.open != b.open || a.mask != b.mask))) {
                same = 0;
                break;
            }
            if (a.tag == HT_APP && !a.digits && !b.digits) {
                if (!enter(s, a.b, 0, 0)) {
                    same = 0;
                    break;
                }
                s->frames[s->frame_count - 1].left = b.b;
                left = a.a;
                right = b.a;
                continue;
            }
            if (a.tag == HT_LAM) {
                left = a.a;
                right = b.a;
                continue;
            }
            if (a.tag == HT_VAR || a.tag == HT_NOMINAL) {
                same = a.uid == b.uid;
            } else if (a.tag == HT_CONST || a.tag == HT_INDEX) {
                same = a.a == b.a;
            } else if (a.tag == HT_NAT) {
                same = !strcmp(a.digits, b.digits);
            } else if (a.tag == HT_APP) {
                same = !a.digits ? string_equal(s, string_of(b), (size_t) b.uid, left) : !b.digits ? string_equal(s, string_of(a), (size_t) a.uid, right) : strings_equal(s, string_of(a), (size_t) a.uid, string_of(b), (size_t) b.uid);
            } else {
                same = a.tag == HT_WILD;
            }
        }
        if (!same || s->frame_count == base) {
            break;
        }
        Frame frame = s->frames[--s->frame_count];
        left = frame.term;
        right = frame.left;
    }
    s->frame_count = base;
    return same;
}

static int rigid(HolTermStore *s, HTerm term)
{
    TermNode n = NODE(s, ht_deref(s, term));
    if (n.tag == HT_CONST && marked(s, n.a, MARK_OPAQUE)) {
        return 0;
    }
    return n.tag == HT_CONST || n.tag == HT_NOMINAL || n.tag == HT_INDEX || n.tag == HT_NAT;
}

static int is_constant(HolTermStore *s, HTerm term)
{
    int tag = NODE(s, ht_deref(s, term)).tag;
    return tag == HT_CONST || tag == HT_NOMINAL || tag == HT_NAT;
}

static size_t level(HolTermStore *s, HTerm term)
{
    return NODE(s, ht_deref(s, term)).scope;
}

static size_t position(HolTermStore *s, HTerm term, const HTerm *terms, size_t count)
{
    for (size_t i = 0; i < count; ++i) {
        if (equal(s, term, terms[i])) return i;
        if (s->error[0]) return SIZE_MAX;
    }
    return SIZE_MAX;
}

/* Raised arguments are usually distinct and ordered. A negative result
    * denotes increasing order, a positive one decreasing order. */
static int atomic_order(HolTermStore *s, HTerm left, HTerm right);
static int argument_order(HolTermStore *s, const HTerm *arguments, size_t count)
{
    int order = 0;
    for (size_t i = 0; i < count; ++i) {
        if (!work_okay(s) || !rigid(s, arguments[i])) return 0;
        if (i) {
            int next = atomic_order(s, arguments[i - 1], arguments[i]);
            if (!next || (order && (next < 0) != (order < 0))) return 0;
            order = next;
        }
    }
    return order < 0 ? -1 : 1;
}

static size_t argument_position(HolTermStore *s, HTerm term, const HTerm *arguments, size_t count, int order)
{
    if (!order || !rigid(s, term)) return position(s, term, arguments, count);
    size_t low = 0, high = count;
    while (low < high) {
        size_t mid = low + (high - low) / 2;
        int compared = atomic_order(s, arguments[mid], term);
        if (!compared) return mid;
        if ((compared < 0) == (order < 0)) low = mid + 1;
        else high = mid;
    }
    return SIZE_MAX;
}

static int pattern(HolTermStore *s, HTerm variable, const HTerm *arguments, size_t count)
{
    int ordered = count >= 8 && argument_order(s, arguments, count);
    if (s->error[0]) return 0;
    size_t scope = level(s, variable);
    for (size_t i = 0; i < count; ++i) {
        if (!rigid(s, arguments[i]) || (is_constant(s, arguments[i]) && level(s, arguments[i]) <= scope)) return 0;
        if (!ordered && (position(s, arguments[i], arguments, i) != SIZE_MAX || s->error[0])) return 0;
    }
    return 1;
}

static int trail_variable(HolTermStore *s, HTerm variable)
{
    if (!reserve(s, s->trail, &s->trail_capacity, s->trail_count + 1, sizeof(*s->trail))) {
        return 0;
    }
    TermNode n = NODE(s, variable);
    s->trail[s->trail_count++] = (Trail) { variable, n.a, n.scope };
    return 1;
}

/* 1 also when the store fails: the caller then finds the error. */
static int occurs(HolTermStore *s, HTerm variable, HTerm term)
{
    size_t base = s->frame_count;
    int found = 0;
    for (;;) {
        if (!work_okay(s)) {
            found = 1;
            break;
        }
        term = ht_deref(s, term);
        if (term == variable) {
            found = 1;
            break;
        }
        TermNode n = NODE(s, term);
        if (!stable(n) && n.tag == HT_APP) {
            if (!enter(s, n.b, 0, 0)) {
                found = 1;
                break;
            }
            term = n.a;
            continue;
        }
        if (!stable(n) && n.tag == HT_LAM) {
            if (n.b != HT_NONE && !enter(s, n.b, 0, 0)) { found = 1; break; }
            term = n.a;
            continue;
        }
        if (s->frame_count == base) {
            break;
        }
        term = s->frames[--s->frame_count].term;
    }
    s->frame_count = base;
    return found;
}

static int lower_scopes(HolTermStore *s, HTerm term, size_t scope)
{
    size_t base = s->frame_count;
    int okay = 1;
    for (;;) {
        hm_count(s->memory, HM_SCOPE_VISITS, 1);
        if (!work_okay(s)) {
            okay = 0;
            break;
        }
        term = ht_deref(s, term);
        TermNode n = NODE(s, term);
        if (!stable(n) && n.tag == HT_APP) {
            if (!enter(s, n.b, 0, 0)) {
                okay = 0;
                break;
            }
            term = n.a;
            continue;
        }
        if (!stable(n) && n.tag == HT_LAM) {
            if (n.b != HT_NONE && !enter(s, n.b, 0, 0)) { okay = 0; break; }
            term = n.a;
            continue;
        }
        if (n.tag == HT_VAR && n.scope > scope) {
            if (!trail_variable(s, term)) {
                okay = 0;
                break;
            }
            NODE(s, term).scope = scope;
            memo_mutated(s, term);
        }
        if (s->frame_count == base) {
            break;
        }
        term = s->frames[--s->frame_count].term;
    }
    s->frame_count = base;
    return okay;
}

/* 1 also when the store fails: the caller then finds the error. */
static int index_free(HolTermStore *s, HTerm term, size_t index)
{
    size_t base = s->frame_count;
    int found = 0;
    for (;;) {
        if (!work_okay(s)) {
            found = 1;
            break;
        }
        term = ht_deref(s, term);
        TermNode n = NODE(s, term);
        if (!closed_below(n, index)) {
            if (stable(n) && index < 32 && (n.mask >> index & 1)) {
                found = 1;
                break;
            }
            if (n.tag == HT_APP) {
                if (!enter(s, n.b, index, 0)) {
                    found = 1;
                    break;
                }
                term = n.a;
                continue;
            }
            if (n.tag == HT_LAM) {
                if (n.b != HT_NONE && !enter(s, n.b, index, 0)) {
                    found = 1;
                    break;
                }
                term = n.a;
                ++index;
                continue;
            }
            if (n.tag == HT_INDEX && n.a == index) {
                found = 1;
                break;
            }
        }
        if (s->frame_count == base) {
            break;
        }
        Frame frame = s->frames[--s->frame_count];
        term = frame.term;
        index = frame.level;
    }
    s->frame_count = base;
    return found;
}

/* Stages of a frame: 0 not visited yet; 1 an application whose function is
    * being reduced; 2 its argument; 3 an abstraction whose body is. An eta step
    * visits the same frame again with the contracted term. */
static HTerm eta_reduce(HolTermStore *s, HTerm root)
{
    size_t base = s->frame_count;
    HTerm result = HT_NONE;
    if (root != HT_NONE && (NODE(s, ht_deref(s, root)).summary & (HS_STABLE | HS_ETA)) == (HS_STABLE | HS_ETA)) {
        return work_okay(s) ? ht_deref(s, root) : HT_NONE;
    }
    if (!enter(s, root, 0, 0)) {
        return HT_NONE;
    }
    while (s->frame_count > base) {
        Frame frame = s->frames[s->frame_count - 1];
        if (frame.stage == 0) {
            if (!work_okay(s)) {
                break;
            }
            HTerm term = ht_deref(s, frame.term);
            TermNode n = NODE(s, term);
            int settled = (n.summary & (HS_STABLE | HS_ETA)) == (HS_STABLE | HS_ETA);
            if (!settled && (n.tag == HT_APP || n.tag == HT_LAM)) {
                s->frames[s->frame_count - 1].term = term;
                s->frames[s->frame_count - 1].stage = n.tag == HT_APP ? 1 : 3;
                if (!enter(s, n.a, 0, 0)) {
                    break;
                }
                continue;
            }
            result = term;
        } else if (frame.stage == 1) {
            s->frames[s->frame_count - 1].left = result;
            s->frames[s->frame_count - 1].stage = 2;
            if (!enter(s, NODE(s, frame.term).b, 0, 0)) {
                break;
            }
            continue;
        } else if (frame.stage == 2) {
            TermNode n = NODE(s, frame.term);
            result = unchanged(s, frame.left, n.a) && unchanged(s, result, n.b) ? frame.term : ht_app(s, frame.left, result, n.meta);
        } else {
            TermNode n = NODE(s, frame.term), body = NODE(s, result);
            if (body.tag == HT_APP) {
                TermNode argument = NODE(s, ht_deref(s, body.b));
                if (argument.tag == HT_INDEX && !argument.a && !index_free(s, body.a, 0)) {
                    HTerm reduced = remove_binder(s, body.a, 0);
                    if (reduced == HT_NONE) {
                        break;
                    }
                    s->frames[s->frame_count - 1].term = reduced;
                    s->frames[s->frame_count - 1].stage = 0;
                    continue;
                }
                if (s->error[0]) {
                    break;
                }
            }
            result = unchanged(s, result, n.a) ? frame.term : ht_lam_typed(s, result, n.meta, n.b);
        }
        if (result == HT_NONE) {
            break;
        }
        --s->frame_count;
    }
    if (s->frame_count > base) {
        s->frame_count = base;
        return HT_NONE;
    }
    return result;
}

/* Pure beta/eta identity: normalization may allocate nodes, but never changes
    * a variable, scope, disagreement or trail. Rigid unequal heads reject
    * before normalizing their (possibly very large) arguments. */
int ht_same(HolTermStore *s, HTerm left, HTerm right)
{
    if (!s || !operation_begin(s)) return -1;
    int result = -1;
    HTSpine lhs = { 0 }, rhs = { 0 };
    left = normalize(s, left, HT_WHNF);
    right = normalize(s, right, HT_WHNF);
    if (left == HT_NONE || right == HT_NONE) goto finish;
    if (left == right) { result = 1; goto finish; }
    if (!ht_spine(s, left, &lhs) || !ht_spine(s, right, &rhs)) goto finish;
    TermNode a = NODE(s, ht_deref(s, lhs.head)), b = NODE(s, ht_deref(s, rhs.head));
    if (a.tag == b.tag && (a.tag == HT_CONST || a.tag == HT_INDEX || a.tag == HT_NOMINAL) && (a.tag == HT_NOMINAL ? a.uid != b.uid : a.a != b.a)) {
        result = 0;
        goto finish;
    }
    /* Identical current syntax is a sufficient beta/eta identity test. This
        * accepts equal open constructor graphs in one comparison traversal,
        * without normalizing every unchanged argument first. A mismatch is
        * inconclusive: beta/eta reduction can still make the terms equal. */
    if (equal(s, left, right)) { result = 1; goto finish; }
    if (s->error[0]) goto finish;
    left = eta_reduce(s, normalize(s, left, HT_NF));
    right = eta_reduce(s, normalize(s, right, HT_NF));
    if (left != HT_NONE && right != HT_NONE) result = equal(s, left, right);
finish:
    ht_spine_free(&lhs);
    ht_spine_free(&rhs);
    operation_end(s);
    return s->error[0] ? -1 : result;
}

static int assign(HolTermStore *s, HTerm variable, HTerm value)
{
    value = eta_reduce(s, ht_normalize(s, value, HT_NF));
    if (value == HT_NONE) {
        return -1;
    }
    if (ht_deref(s, variable) == value) {
        return 1;
    }
    if (occurs(s, variable, value)) {
        return s->error[0] ? -1 : 0;
    }
    if (!lower_scopes(s, value, NODE(s, variable).scope) || !trail_variable(s, variable)) {
        return -1;
    }
    if (NODE(s, value).open) s->binding_has_loose_indices = 1;
    NODE(s, variable).a = value;
    memo_mutated(s, variable);
    ++s->changes;
    return 1;
}

/* Whether term is literally head applied to these arguments. A bound variable
    * in between does not count: building the value again removes it, so that a
    * value whose variables are all bound becomes stable. */
static int same_applications(const HolTermStore *s, HTerm term, HTerm head, const HTerm *arguments, size_t count)
{
    while (count) {
        TermNode n = NODE(s, term);
        if (n.tag != HT_APP || n.b != arguments[--count]) {
            return 0;
        }
        term = n.a;
    }
    return term == head;
}

static HTerm applications(HolTermStore *s, HTerm head, const HTerm *arguments, size_t count)
{
    for (size_t i = 0; i < count && head != HT_NONE; ++i) {
        head = ht_app(s, head, arguments[i], -1);
    }
    return head;
}

/* Types contain the same type variables as the terms of the run. These
    * helpers only project and rebuild an already checked arrow type. */
static HTerm arrow_result(HolTermStore *s, HTerm type, HTerm *domain)
{
    type = ht_deref(s, type);
    if (type == HT_NONE || NODE(s, type).tag != HT_APP) return HT_NONE;
    TermNode result = NODE(s, type);
    HTerm prefix = ht_deref(s, result.a);
    if (prefix == HT_NONE || NODE(s, prefix).tag != HT_APP) return HT_NONE;
    HTerm head = ht_deref(s, NODE(s, prefix).a);
    if (head == HT_NONE || NODE(s, head).tag != HT_CONST || NODE(s, head).a != s->arrow) return HT_NONE;
    *domain = NODE(s, prefix).b;
    return result.b;
}

static HTerm split_type(HolTermStore *s, HTerm type, size_t count, Terms *domains)
{
    for (size_t i = 0; i < count && type != HT_NONE; ++i) {
        if (!work_okay(s)) return HT_NONE;
        HTerm domain = HT_NONE;
        type = arrow_result(s, type, &domain);
        if (type == HT_NONE || !push_term(s, domains, domain)) return HT_NONE;
    }
    return type;
}

static HTerm common_type(HolTermStore *s, HTerm variable, size_t arity, const HTerm *arguments, size_t count)
{
    Terms domains = { 0 }, selected = { 0 };
    HTerm result = split_type(s, ht_type(s, variable), arity, &domains);
    for (size_t i = 0; result != HT_NONE && i < count; ++i) {
        if (!work_okay(s)) { result = HT_NONE; break; }
        HTerm argument = ht_deref(s, arguments[i]);
        HTerm type = HT_NONE;
        if (argument != HT_NONE) {
            TermNode n = NODE(s, argument);
            type = n.tag == HT_INDEX && n.a < domains.count ? domains.items[domains.count - n.a - 1] : ht_type(s, argument);
        }
        if (type == HT_NONE || !push_term(s, &selected, type)) result = HT_NONE;
    }
    if (result != HT_NONE && count) {
        HTerm arrow = ht_constant(s, s->arrow, -1);
        while (selected.count && result != HT_NONE) {
            HTerm prefix = ht_app(s, arrow, selected.items[--selected.count], -1);
            result = prefix == HT_NONE ? HT_NONE : ht_app(s, prefix, result, -1);
        }
    }
    hm_free(domains.items);
    hm_free(selected.items);
    return result;
}

static HTerm abstractions_typed(HolTermStore *s, HTerm body, const Binder *hints, size_t count, HTerm type)
{
    Terms domains = { 0 };
    if (split_type(s, type, count, &domains) == HT_NONE) domains.count = 0;
    while (count && body != HT_NONE) {
        --count;
        body = ht_lam_typed(s, body, hints[count].meta, count < domains.count ? domains.items[count] : hints[count].type);
    }
    hm_free(domains.items);
    return body;
}

static HTerm abstractions(HolTermStore *s, HTerm body, const Binder *hints, size_t count)
{
    while (count && body != HT_NONE) {
        Binder hint = hints[--count];
        body = ht_lam_typed(s, body, hint.meta, hint.type);
    }
    return body;
}

static Binder parameter_hint(HolTermStore *s, HTerm parameter, const Binders *outer)
{
    TermNode n = NODE(s, ht_deref(s, parameter));
    if (n.tag == HT_NOMINAL || n.tag == HT_VAR) {
        return (Binder) { n.meta, n.b };
    }
    if (n.tag == HT_INDEX && n.a < outer->count) {
        return outer->items[outer->count - n.a - 1];
    }
    return (Binder) { -1, HT_NONE };
}

static int parameter_hints(HolTermStore *s, const HTerm *parameters, size_t count, const Binders *outer, Binders *hints)
{
    for (size_t i = 0; i < count; ++i) {
        if (!push_binder(s, hints, parameter_hint(s, parameters[i], outer))) {
            return 0;
        }
    }
    return 1;
}

static int lhs_arguments(HolTermStore *s, const HTerm *parameters, size_t count, size_t binders, Terms *result)
{
    for (size_t i = 0; i < count; ++i) {
        if (!push_term(s, result, shift(s, parameters[i], binders, 0))) {
            return 0;
        }
    }
    for (size_t i = binders; i > 0; --i) {
        if (!push_term(s, result, ht_index(s, i - 1))) {
            return 0;
        }
    }
    return 1;
}

static int atomic_order(HolTermStore *s, HTerm left, HTerm right)
{
    TermNode a = NODE(s, ht_deref(s, left)), b = NODE(s, ht_deref(s, right));
    int rank_a = a.tag == HT_INDEX ? 1 : 0;
    int rank_b = b.tag == HT_INDEX ? 1 : 0;
    if (rank_a != rank_b) {
        return rank_a < rank_b ? -1 : 1;
    }
    if (a.tag == HT_INDEX && b.tag == HT_INDEX) {
        return a.a < b.a ? -1 : a.a > b.a;
    }
    if (a.tag == HT_NOMINAL && b.tag == HT_NOMINAL) {
        return a.uid < b.uid ? -1 : a.uid > b.uid;
    }
    if (a.tag != b.tag) {
        return a.tag < b.tag ? -1 : 1;
    }
    if (a.tag == HT_NAT) {
        size_t al = strlen(a.digits), bl = strlen(b.digits);
        return al == bl ? strcmp(a.digits, b.digits) : al < bl ? -1 : 1;
    }
    return a.a < b.a ? -1 : a.a > b.a;
}

static int common_arguments(HolTermStore *s, const Terms *left, const HTSpine *right, Terms *common)
{
    int order = left->count >= 8 && right->count >= 8 ? argument_order(s, right->args, right->count) : 0;
    if (s->error[0]) return 0;
    for (size_t i = 0; i < left->count; ++i) {
        if (s->error[0]) return 0;
        if (argument_position(s, left->items[i], right->args, right->count, order) != SIZE_MAX && !push_term(s, common, left->items[i])) {
            return 0;
        }
    }
    if (common->count >= 8) {
        int sorted = argument_order(s, common->items, common->count);
        if (s->error[0]) return 0;
        if (sorted > 0) {
            for (size_t i = 0; i < common->count / 2; ++i) {
                size_t j = common->count - i - 1;
                HTerm item = common->items[i];
                common->items[i] = common->items[j];
                common->items[j] = item;
            }
        }
        if (sorted) return 1;
    }
    for (size_t i = 1; i < common->count; ++i) {
        HTerm value = common->items[i];
        size_t j = i;
        while (j && atomic_order(s, value, common->items[j - 1]) < 0) {
            common->items[j] = common->items[j - 1];
            --j;
        }
        common->items[j] = value;
    }
    return 1;
}

static int down(HolTermStore *s, const HTerm *selected, size_t count, const HTerm *arguments, size_t arity, Terms *result)
{
    int order = count >= 8 && arity >= 8 ? argument_order(s, arguments, arity) : 0;
    if (s->error[0]) return 0;
    for (size_t i = 0; i < count; ++i) {
        if (s->error[0]) return 0;
        size_t index = argument_position(s, selected[i], arguments, arity, order);
        if (index != SIZE_MAX && !push_term(s, result, ht_index(s, arity - index - 1))) {
            return 0;
        }
    }
    return 1;
}

static int visible_constants(HolTermStore *s, const HTerm *arguments, size_t count, size_t scope, Terms *result)
{
    for (size_t i = 0; i < count; ++i) {
        if (is_constant(s, arguments[i]) && level(s, arguments[i]) <= scope && !push_term(s, result, arguments[i])) {
            return 0;
        }
    }
    return 1;
}

/* A value whose parts are still being bound: an abstraction waiting for its
    * body, or a rigid head waiting for the arguments from next on. */
typedef struct {
    HTerm value, head;
    HTerm *args;
    size_t count, next;
    Terms results;
    int lambda;
    int64_t meta;
} Binding;

typedef struct { Binding *items; size_t count, capacity; } Bindings;

/* The value is an application or an atom in head normal form. A rigid head
    * leaves its arguments in *pending, to be bound next; without arguments, and
    * for a flexible head, *result is the bound value.
    * 2 means that a non-pattern equation must be delayed. */
/* 1: the term is a type, built of constructors of types and of type variables
    * alone; 0: it is not, as the value that a host applied a wildcard to is not;
    * -1: store error. A type of any size is read: the work limit of the store is
    * the only bound, and reaching it is that error. */
static int type_term(HolTermStore *s, HTerm root)
{
    size_t base = s->frame_count;
    int result = enter(s, root, 0, 0) ? 1 : -1;
    while (result == 1 && s->frame_count > base) {
        HTerm term = ht_deref(s, s->frames[--s->frame_count].term);
        if (term == HT_NONE || !work_okay(s)) {
            result = -1;
            break;
        }
        TermNode n = NODE(s, term);
        if (n.tag == HT_CONST) result = marked(s, n.a, MARK_TYPE) != 0;
        else if (n.tag == HT_VAR) result = n.is_type != 0;
        else if (n.tag != HT_APP || n.digits) result = 0;
        else if (!enter(s, n.b, 0, 0) || !enter(s, n.a, 0, 0)) result = -1;
    }
    s->frame_count = base;
    return result;
}

static int bind_spine(HolTermStore *s, HTerm variable, HTerm value, const HTerm *parameters, size_t arity, const Binders *outer, const Binders *bound, int whole, Binding *pending, HTerm *result)
{
    HTSpine rhs = { 0 };
    Terms lhs = { 0 }, common = { 0 }, lhs_args = { 0 }, rhs_args = { 0 };
    Binders hints = { 0 }, rhs_hints = { 0 };
    int status = -1;
    *pending = (Binding) { value, HT_NONE, NULL, 0, 0, { 0 }, 0, -1 };
    if (!ht_spine(s, value, &rhs)) {
        goto finish;
    }
    HTerm head = ht_deref(s, rhs.head);
    TermNode h = NODE(s, head);
    if (h.tag == HT_WILD) {
        /* The compiler gives the wildcard of a program its type as its first
            * argument; the arguments after it are those of the value that the
            * wildcard stands for. A wildcard without arguments that is the whole
            * value has the type of what it is bound to. */
        HTerm type = HT_NONE;
        if (NODE(s, variable).is_type) {
            /* a type has no type */
        } else if (rhs.count) {
            int typed = type_term(s, rhs.args[0]);
            if (typed < 0) {
                if (!s->error[0]) fail(s, "Invalid wildcard annotation");
                goto finish;
            }
            if (typed) {
                Terms domains = { 0 };
                type = split_type(s, rhs.args[0], rhs.count - 1, &domains);
                hm_free(domains.items);
            }
        } else if (whole) {
            type = common_type(s, variable, arity + bound->count, NULL, 0);
        }
        if (s->error[0]) goto finish;
        *result = ht_var_typed(s, NODE(s, variable).scope, NODE(s, variable).is_type, -1, type);
        status = *result == HT_NONE ? -1 : 1;
        goto finish;
    }
    if (rigid(s, head)) {
        HTerm output_head = HT_NONE;
        /* A bound index keeps its place. The shifted parameters all have
            * indices above this suffix, so no search can change the answer. */
        if ((h.tag == HT_INDEX && h.a < bound->count) || (is_constant(s, head) && level(s, head) <= NODE(s, variable).scope)) {
            output_head = head;
        } else {
            if (!lhs_arguments(s, parameters, arity, bound->count, &lhs)) goto finish;
            size_t index = position(s, head, lhs.items, lhs.count);
            if (index == SIZE_MAX) {
                status = 0;
                goto finish;
            }
            output_head = h.tag == HT_INDEX && h.a == lhs.count - index - 1 ? head : ht_index(s, lhs.count - index - 1);
        }
        pending->head = output_head;
        if (rhs.args != rhs.few) {
            pending->args = rhs.args;
            rhs.args = NULL;
        } else if (rhs.count) {
            pending->args = hm_alloc(s->memory, rhs.count * sizeof(*pending->args));
            if (!pending->args) {
                fail(s, "Term allocation failed");
                goto finish;
            }
            memcpy(pending->args, rhs.few, rhs.count * sizeof(*pending->args));
        }
        pending->count = rhs.count;
        *result = output_head;
        status = output_head == HT_NONE ? -1 : 1;
        goto finish;
    }
    if (h.tag != HT_VAR || head == variable) {
        status = 0;
        goto finish;
    }
    int preserve_witness = (h.pinned | NODE(s, variable).pinned) & 4;
    if (!preserve_witness && !rhs.count && h.scope <= NODE(s, variable).scope && h.is_type == NODE(s, variable).is_type && (h.b != HT_NONE || !whole)) {
        *result = head;
        status = 1;
        goto finish;
    }
    if (!lhs_arguments(s, parameters, arity, bound->count, &lhs)) goto finish;
    for (size_t i = 0; i < rhs.count; ++i) {
        rhs.args[i] = ht_normalize(s, rhs.args[i], HT_NF);
        if (rhs.args[i] == HT_NONE) {
            goto finish;
        }
    }
    if (!common_arguments(s, &lhs, &rhs, &common)) {
        goto finish;
    }
    for (size_t i = 0; i < outer->count; ++i) {
        if (!push_binder(s, &hints, outer->items[i])) {
            goto finish;
        }
    }
    for (size_t i = 0; i < bound->count; ++i) {
        if (!push_binder(s, &hints, bound->items[i])) {
            goto finish;
        }
    }
    if (!parameter_hints(s, rhs.args, rhs.count, &hints, &rhs_hints)) {
        goto finish;
    }
    size_t left_scope = NODE(s, variable).scope, right_scope = h.scope;
    if (pattern(s, head, rhs.args, rhs.count)) {
        if (left_scope < right_scope) {
            if (!visible_constants(s, lhs.items, lhs.count, right_scope, &rhs_args) || !down(s, rhs_args.items, rhs_args.count, lhs.items, lhs.count, &lhs_args)) {
                goto finish;
            }
        } else {
            if (!visible_constants(s, rhs.args, rhs.count, left_scope, &lhs_args) || !down(s, lhs_args.items, lhs_args.count, rhs.args, rhs.count, &rhs_args)) {
                goto finish;
            }
        }
        if (!down(s, common.items, common.count, lhs.items, lhs.count, &lhs_args) || !down(s, common.items, common.count, rhs.args, rhs.count, &rhs_args)) {
            goto finish;
        }
    } else {
        int beta_pattern = left_scope >= right_scope;
        for (size_t i = 0; i < rhs.count; ++i) {
            if (!rigid(s, rhs.args[i]) || (is_constant(s, rhs.args[i]) && level(s, rhs.args[i]) <= right_scope)) {
                beta_pattern = 0;
            }
        }
        if (!beta_pattern) {
            status = 2;
            goto finish;
        }
        for (size_t i = 0; i < rhs.count; ++i) {
            HTerm argument = rhs.args[i];
            int visible = is_constant(s, argument) && level(s, argument) <= left_scope;
            size_t index = position(s, argument, lhs.items, lhs.count);
            if (visible || index != SIZE_MAX) {
                if (!push_term(s, &rhs_args, ht_index(s, rhs.count - i - 1)) || !push_term(s, &lhs_args, visible ? argument : ht_index(s, lhs.count - index - 1))) {
                    goto finish;
                }
            }
        }
    }
    HTerm type = common_type(s, head, rhs.count, rhs_args.items, rhs_args.count);
    if (s->error[0]) goto finish;
    /* An identity projection only renames the head. Preserve its identity
        * and exact type instead, unless the full path must recover a type. */
    int identity = rhs_args.count == rhs.count;
    for (size_t i = 0; identity && i < rhs.count; ++i) {
        TermNode selected = NODE(s, ht_deref(s, rhs_args.items[i]));
        identity = selected.tag == HT_INDEX && selected.a == rhs.count - i - 1;
    }
    if (!preserve_witness && identity && h.scope <= NODE(s, variable).scope && h.is_type == NODE(s, variable).is_type && (type != HT_NONE || (h.b == HT_NONE && !whole))) {
        *result = applications(s, head, lhs_args.items, lhs_args.count);
        status = *result == HT_NONE ? -1 : 1;
        goto finish;
    }

    if (type == HT_NONE && whole && !s->error[0]) type = common_type(s, variable, lhs.count, lhs_args.items, lhs_args.count);
    HTerm common_head = ht_var_typed(s, left_scope, NODE(s, variable).is_type || h.is_type, -1, type);
    HTerm right_body = applications(s, common_head, rhs_args.items, rhs_args.count);
    HTerm replacement = abstractions_typed(s, right_body, rhs_hints.items, rhs_hints.count, h.b);
    if (replacement == HT_NONE) {
        goto finish;
    }
    status = assign(s, head, replacement);
    if (status == 1) {
        *result = applications(s, common_head, lhs_args.items, lhs_args.count);
        if (*result == HT_NONE) {
            status = -1;
        }
    }
finish:
    ht_spine_free(&rhs);
    hm_free(lhs.items);
    hm_free(common.items);
    hm_free(lhs_args.items);
    hm_free(rhs_args.items);
    hm_free(hints.items);
    hm_free(rhs_hints.items);
    return s->error[0] ? -1 : status;
}

/* The value of the variable applied to the parameters: value with every
    * parameter and every binder of its own replaced by an index. The pending
    * parts are kept in an array, not on the C stack.
    * 2 means that a non-pattern equation must be delayed. */
static int bind_value(HolTermStore *s, HTerm variable, HTerm value, const HTerm *parameters, size_t arity, const Binders *outer, Binders *bound, HTerm *result)
{
    Bindings pending = { NULL, 0, 0 };
    size_t hints = bound->count;
    int status = 1, descending = 1;
    size_t rigid_depth = 0;
    while (status == 1) {
        if (descending) {
            status = -1;
            hm_count(s->memory, HM_BIND_VISITS, 1);
            if (!work_okay(s)) {
                break;
            }
            value = ht_normalize(s, value, HT_HNF);
            if (value == HT_NONE) {
                break;
            }
            TermNode n = NODE(s, value);
            /* nothing below is a parameter, a variable or out of the variable's scope */
            if ((stable(n) && n.scope <= NODE(s, variable).scope && closed_below(n, bound->count)) || n.tag == HT_NAT) {
                *result = value;
                status = 1;
                descending = 0;
                continue;
            }
            Binding part = { value, HT_NONE, NULL, 0, 0, { 0 }, 1, n.meta };
            if (n.tag != HT_LAM) {
                status = bind_spine(s, variable, value, parameters, arity, outer, bound, !rigid_depth, &part, result);
                if (status != 1 || !part.count) {
                    hm_free(part.args);
                    descending = 0;
                    continue;
                }
                status = -1;
            }
            if ((part.lambda && !push_binder(s, bound, (Binder) { n.meta, n.b })) || !reserve(s, pending.items, &pending.capacity, pending.count + 1, sizeof(*pending.items))) {
                hm_free(part.args);
                break;
            }
            pending.items[pending.count++] = part;
            if (!part.lambda) ++rigid_depth;
            value = part.lambda ? n.a : part.args[0];
            status = 1;
        } else if (!pending.count) {
            break;
        } else {
            Binding *top = &pending.items[pending.count - 1];
            if (top->lambda) {
                --bound->count;
                *result = *result == NODE(s, top->value).a ? top->value : ht_lam_typed(s, *result, top->meta, NODE(s, top->value).b);
            } else if (!push_term(s, &top->results, *result)) {
                status = -1;
                break;
            } else if (++top->next < top->count) {
                value = top->args[top->next];
                descending = 1;
                continue;
            } else {
                *result = same_applications(s, top->value, top->head, top->results.items, top->results.count) ? top->value : applications(s, top->head, top->results.items, top->results.count);
                hm_free(top->args);
                hm_free(top->results.items);
                --rigid_depth;
            }
            --pending.count;
            if (*result == HT_NONE) {
                status = -1;
            }
        }
    }
    while (pending.count) {
        Binding *top = &pending.items[--pending.count];
        hm_free(top->args);
        hm_free(top->results.items);
    }
    hm_free(pending.items);
    bound->count = hints;
    return s->error[0] ? -1 : status;
}

static int make_substitution(HolTermStore *s, HTerm variable, HTerm rhs, const HTerm *parameters, size_t arity, const Binders *outer)
{
    /* Normality alone does not authorize sharing. The simple-shape proof
        * admits constructors and flex applications to distinct, increasing
        * nominals outside the head's scope. The final scope bound makes all
        * those arguments visible, so binding would retain them unchanged.
        * Lambdas, indices, non-patterns and missing whole types use HOPU. */
    OpenMemo memo;
    if (!arity && !outer->count && !stable(NODE(s, rhs)) && !NODE(s, variable).is_type && !(NODE(s, variable).pinned & 4)
        && NODE(s, variable).b != HT_NONE && open_memo(s, rhs, &memo)
        && memo.simple && (memo.exact || (memo.rigid && !memo.value_types))
        && memo.variables <= variable && memo.scope <= NODE(s, variable).scope) {
        if (!trail_variable(s, variable)) return -1;
        if (NODE(s, rhs).open) s->binding_has_loose_indices = 1;
        NODE(s, variable).a = rhs;
        memo_mutated(s, variable);
        ++s->changes;
        return 1;
    }
    if (s->error[0]) return -1;
    HTCheckpoint checkpoint = ht_checkpoint(s);
    uint64_t changes = s->changes;
    Terms normalized = { 0 }, lhs = { 0 }, common = { 0 };
    Binders lambda_hints = { 0 }, hints = { 0 }, bound = { 0 };
    HTSpine body_spine = { 0 };
    int status = -1;
    rhs = ht_normalize(s, rhs, HT_NF);
    if (rhs == HT_NONE) {
        goto finish;
    }
    for (size_t i = 0; i < arity; ++i) {
        if (!push_term(s, &normalized, ht_normalize(s, parameters[i], HT_NF))) {
            goto finish;
        }
    }
    HTerm body = rhs;
    while (NODE(s, body).tag == HT_LAM) {
        TermNode n = NODE(s, body);
        if (!push_binder(s, &lambda_hints, (Binder) { n.meta, n.b })) {
            goto finish;
        }
        body = ht_deref(s, n.a);
    }
    if (!ht_spine(s, body, &body_spine)) {
        goto finish;
    }
    if (ht_deref(s, body_spine.head) == variable) {
        if (!lhs_arguments(s, normalized.items, normalized.count, lambda_hints.count, &lhs)) {
            goto finish;
        }
        if (lhs.count != body_spine.count) {
            status = 2;
            goto finish;
        }
        int identical = 1;
        for (size_t i = 0; i < lhs.count; ++i) {
            if (equal(s, lhs.items[i], body_spine.args[i])) {
                if (!push_term(s, &common, ht_index(s, lhs.count - i - 1))) {
                    goto finish;
                }
            } else {
                identical = 0;
            }
        }
        if (identical) {
            status = 1;
            goto finish;
        }
        if (!pattern(s, variable, body_spine.args, body_spine.count)) {
            status = 2;
            goto finish;
        }
        if (!parameter_hints(s, normalized.items, normalized.count, outer, &hints)) {
            goto finish;
        }
        for (size_t i = 0; i < lambda_hints.count; ++i) {
            if (!push_binder(s, &hints, lambda_hints.items[i])) {
                goto finish;
            }
        }
        HTerm type = common_type(s, variable, hints.count, common.items, common.count);
        HTerm head = ht_var_typed(s, NODE(s, variable).scope, NODE(s, variable).is_type, -1, type);
        HTerm replacement = abstractions_typed(s, applications(s, head, common.items, common.count), hints.items, hints.count, ht_type(s, variable));
        status = replacement == HT_NONE ? -1 : assign(s, variable, replacement);
    } else {
        if (!pattern(s, variable, normalized.items, normalized.count)) {
            status = 2;
            goto finish;
        }
        HTerm replacement = HT_NONE;
        status = bind_value(s, variable, rhs, normalized.items, normalized.count, outer, &bound, &replacement);
        if (status != 1) {
            goto finish;
        }
        if (!parameter_hints(s, normalized.items, normalized.count, outer, &hints)) {
            status = -1;
            goto finish;
        }
        replacement = abstractions_typed(s, replacement, hints.items, hints.count, ht_type(s, variable));
        status = replacement == HT_NONE ? -1 : assign(s, variable, replacement);
    }
finish:
    hm_free(normalized.items);
    hm_free(lhs.items);
    hm_free(common.items);
    hm_free(lambda_hints.items);
    hm_free(hints.items);
    hm_free(bound.items);
    ht_spine_free(&body_spine);
    if (status != 1) {
        ht_restore(s, checkpoint);
        s->changes = changes;
    }
    return s->error[0] ? -1 : status;
}

static int add_equation(HolTermStore *s, Equations *equations, HTerm left, HTerm right)
{
    if (left == HT_NONE || right == HT_NONE || !reserve(s, equations->items, &equations->capacity, equations->count + 1, sizeof(*equations->items))) {
        return 0;
    }
    equations->items[equations->count++] = (Equation) { left, right };
    return 1;
}

/* known is the value of s->changes at which left and right were in normal
    * form; they are still in normal form while nothing has been bound since. The
    * body of an abstraction and the first argument of a rigid term are solved
    * next; the other arguments wait in s->pairs, each with the number of binders
    * above it, so neither a long list nor a deep argument nests. */
static int solve_pair(HolTermStore *s, HTerm left, HTerm right, Binders *outer, Equations *delayed)
{
    HTSpine lhs = { 0 }, rhs = { 0 };
    size_t base = s->pair_count, binders = outer->count;
    uint64_t known = 0;
    int reduced = 0, status;
    for (;;) {
        for (;;) {
            status = -1;
            if (!work_okay(s)) {
                break;
            }
            left = ht_deref(s, left);
            right = ht_deref(s, right);
            if (left == HT_NONE || right == HT_NONE) {
                fail(s, "Invalid term reference");
                break;
            }
            if (left == right) { status = 1; break; }
            TermNode first = NODE(s, left), second = NODE(s, right);
            if (!outer->count && ((first.tag == HT_VAR && second.ground) || (second.tag == HT_VAR && first.ground))) {
                HTerm variable = first.tag == HT_VAR ? left : right;
                HTerm value = first.tag == HT_VAR ? right : left;
                /* Ground is set only for closed, already-normal constructor
                    * trees without variables, nominals, opaque heads or redexes. */
                if (!trail_variable(s, variable)) break;
                NODE(s, variable).a = value;
                memo_mutated(s, variable);
                ++s->changes;
                status = 1;
                break;
            }
            if (!outer->count && ((first.tag == HT_VAR && (second.summary & HS_RIGID_HEAD))
                || (second.tag == HT_VAR && (first.summary & HS_RIGID_HEAD)))) {
                HTerm variable = first.tag == HT_VAR ? left : right;
                HTerm value = first.tag == HT_VAR ? right : left;
                /* The empty argument list is a pattern. Its rigid opponent
                    * cannot hide a lambda or share the variable's head.
                    * make_substitution performs its own exact NF/scope checks. */
                status = make_substitution(s, variable, value, NULL, 0, outer);
                if (status != 2) break;
                left = ht_normalize(s, left, HT_NF);
                right = ht_normalize(s, right, HT_NF);
                status = add_equation(s, delayed, left, right) ? 1 : -1;
                break;
            }
            /* A constructor head cannot change when one of its arguments is
                * bound. Unify those arguments in the usual left-to-right
                * order, normalizing each when it actually needs HOPU. */
            if ((first.summary & second.summary & HS_RIGID_HEAD)
                && first.tag == HT_APP && second.tag == HT_APP
                && !(normal(first) && normal(second))) {
                do {
                    if (!work_okay(s) || !reserve(s, s->pairs, &s->pair_capacity, s->pair_count + 1, sizeof(*s->pairs))) goto finish;
                    s->pairs[s->pair_count++] = (Pair) { first.b, second.b, outer->count, 0, 0 };
                    first = NODE(s, first.a);
                    second = NODE(s, second.a);
                } while (first.tag == HT_APP && second.tag == HT_APP);
                status = first.tag == HT_CONST && second.tag == HT_CONST && first.a == second.a;
                break;
            }
            if (!reduced || s->changes != known) {
                left = ht_normalize(s, left, HT_NF);
                right = ht_normalize(s, right, HT_NF);
                known = s->changes;
            }
            reduced = 1;
            if (left == HT_NONE || right == HT_NONE) {
                break;
            }
            if (left == right) {
                status = 1;
                break;
            }
            TermNode l = NODE(s, left), r = NODE(s, right);
            if (normal(l) && normal(r)) {
                status = equal(s, left, right);
                break;
            }
            if (l.tag == HT_LAM && r.tag == HT_LAM) {
                if (!push_binder(s, outer, (Binder) { l.meta, l.b != HT_NONE ? l.b : r.b })) {
                    break;
                }
                left = l.a;
                right = r.a;
                continue;
            }
            ht_spine_free(&lhs);
            ht_spine_free(&rhs);
            if (!spine_view(s, left, &lhs) || !spine_view(s, right, &rhs)) {
                break;
            }
            HTerm lh = ht_deref(s, lhs.head), rh = ht_deref(s, rhs.head);
            if ((l.tag == HT_LAM && rigid(s, rh)) || (r.tag == HT_LAM && rigid(s, lh))) {
                int left_lambda = l.tag == HT_LAM;
                HTerm expansion = shift(s, left_lambda ? right : left, 1, 0);
                HTerm index = ht_index(s, 0);
                expansion = ht_app(s, expansion, index, -1);
                if (expansion == HT_NONE || !push_binder(s, outer, (Binder) { left_lambda ? l.meta : r.meta, left_lambda ? l.b : r.b })) {
                    break;
                }
                left = left_lambda ? l.a : expansion;
                right = left_lambda ? expansion : r.a;
                continue;
            }
            if (rigid(s, lh) && rigid(s, rh)) {
                if (!equal(s, lh, rh) || lhs.count != rhs.count) {
                    status = 0;
                    break;
                }
                status = 1;
                if (!lhs.count) {
                    break;
                }
                if (lhs.count - 1 > SIZE_MAX - s->pair_count || !reserve(s, s->pairs, &s->pair_capacity, s->pair_count + lhs.count - 1, sizeof(*s->pairs))) {
                    status = -1;
                    break;
                }
                for (size_t i = lhs.count; i > 1; --i) {
                    s->pairs[s->pair_count++] = (Pair) { lhs.args[i - 1], rhs.args[i - 1], outer->count, known, 1 };
                }
                left = lhs.args[0];
                right = rhs.args[0];
                continue;
            }
            if (equal(s, left, right)) {
                status = 1;
            } else if (!lhs.count && !rhs.count && !outer->count
                && NODE(s, lh).tag == HT_VAR && NODE(s, rh).tag == HT_VAR
                && NODE(s, lh).is_type == NODE(s, rh).is_type
                && NODE(s, lh).b != HT_NONE && NODE(s, rh).b != HT_NONE
                && !((NODE(s, lh).pinned | NODE(s, rh).pinned) & 4)
                && NODE(s, lh < rh ? lh : rh).scope <= NODE(s, lh < rh ? rh : lh).scope) {
                status = assign(s, lh < rh ? rh : lh, lh < rh ? lh : rh);
            } else if (NODE(s, lh).tag == HT_VAR && pattern(s, lh, lhs.args, lhs.count)) {
                status = make_substitution(s, lh, right, lhs.args, lhs.count, outer);
            } else if (NODE(s, rh).tag == HT_VAR && pattern(s, rh, rhs.args, rhs.count)) {
                status = make_substitution(s, rh, left, rhs.args, rhs.count, outer);
            } else if (NODE(s, lh).tag == HT_WILD || NODE(s, rh).tag == HT_WILD) {
                status = 1;
            } else {
                status = 2;
            }
            if (status == 2) {
                HTerm a = abstractions(s, left, outer->items, outer->count);
                HTerm b = abstractions(s, right, outer->items, outer->count);
                status = add_equation(s, delayed, a, b) ? 1 : -1;
            }
            break;
        }
        if (status != 1 || s->error[0] || s->pair_count == base) {
            break;
        }
        Pair next = s->pairs[--s->pair_count];
        left = next.left;
        right = next.right;
        known = next.known;
        reduced = next.reduced;
        outer->count = next.binders;
    }
finish:
    s->pair_count = base;
    outer->count = binders;
    ht_spine_free(&lhs);
    ht_spine_free(&rhs);
    return s->error[0] ? -1 : status;
}

/* A compiled clause head with an immutable rigid spine shares its predicate
    * with the goal. Instantiate its arguments, without building application
    * nodes for the predicate only to take them apart again. Keep the original
    * logical order and solve all pairs in one transaction with disagreements. */
static int instance_equations(HolTermStore *s, Equations *input, HTerm left, HTerm right, const HTerm *values, size_t count)
{
    size_t base = s->pair_count;
    int status = 1;
    for (;;) {
        left = ht_deref(s, left);
        right = ht_deref(s, right);
        if (left == HT_NONE || right == HT_NONE || !work_okay(s)) { status = -1; break; }
        TermNode goal = NODE(s, left), pattern = NODE(s, right);
        if (!closed_below(pattern, 0) && (goal.summary & pattern.summary & HS_RIGID_HEAD)
            && goal.tag == HT_APP && pattern.tag == HT_APP) {
            do {
                if (!work_okay(s) || !reserve(s, s->pairs, &s->pair_capacity, s->pair_count + 1, sizeof(*s->pairs))) { status = -1; goto done; }
                s->pairs[s->pair_count++] = (Pair) { goal.b, pattern.b, 0, 0, 0 };
                goal = NODE(s, goal.a);
                pattern = NODE(s, pattern.a);
            } while (goal.tag == HT_APP && pattern.tag == HT_APP);
            if (goal.tag != HT_CONST || pattern.tag != HT_CONST || goal.a != pattern.a) { status = 0; break; }
        } else {
            if (pattern.tag == HT_INDEX && pattern.a < count) right = values[count - 1 - pattern.a];
            else if (!closed_below(pattern, 0)) right = instantiate(s, right, values, count, 0);
            if (!add_equation(s, input, left, right)) { status = -1; break; }
        }
        if (s->pair_count == base) break;
        Pair next = s->pairs[--s->pair_count];
        left = next.left;
        right = next.right;
    }
done:
    s->pair_count = base;
    return status;
}

static int unify_equations(HolTermStore *s, HTerm left, HTerm right, int add_new, const HTerm *values, size_t count)
{
    if (!s || s->error[0]) {
        return -1;
    }
    HTCheckpoint checkpoint = ht_checkpoint(s);
    uint64_t initial_changes = s->changes;
    /* The buffers of the store are borrowed unless a unification is running. */
    int borrowed = !s->unifying;
    Equations input = { 0 }, output = { 0 };
    Binders outer = { 0 };
    if (borrowed) {
        input = s->solving;
        output = s->delayed;
        outer = s->binders;
        input.count = 0;
        output.count = 0;
        outer.count = 0;
        s->unifying = 1;
    }
    int status = -1;
    if (values) {
        int matched = instance_equations(s, &input, left, right, values, count);
        if (matched != 1) { status = matched; goto finish; }
    } else if (add_new && !add_equation(s, &input, left, right)) {
        goto finish;
    }
    for (size_t item = s->pending_head; item != HT_NONE; item = s->pending[item].next) {
        Pending p = s->pending[item];
        if (!add_equation(s, &input, p.left, p.right)) {
            goto finish;
        }
    }
    for (;;) {
        uint64_t changes = s->changes;
        output.count = 0;
        status = 1;
        for (size_t i = 0; i < input.count && status == 1; ++i) {
            status = solve_pair(s, input.items[i].left, input.items[i].right, &outer, &output);
        }
        if (status != 1) {
            goto finish;
        }
        if (!output.count || s->changes == changes) {
            break;
        }
        Equations swap = input;
        input = output;
        output = swap;
    }
    s->pending_head = HT_NONE;
    for (size_t i = output.count; i > 0; --i) {
        if (!reserve(s, s->pending, &s->pending_capacity, s->pending_count + 1, sizeof(*s->pending))) {
            status = -1;
            goto finish;
        }
        Equation eq = output.items[i - 1];
        s->pending[s->pending_count] = (Pending) { eq.left, eq.right, s->pending_head };
        s->pending_head = s->pending_count++;
    }
finish:
    if (borrowed) {
        s->solving = input;
        s->delayed = output;
        s->binders = outer;
        s->unifying = 0;
    } else {
        hm_free(input.items);
        hm_free(output.items);
        hm_free(outer.items);
    }
    if (status != 1) {
        ht_restore(s, checkpoint);
        s->changes = initial_changes;
    }
    return s->error[0] ? -1 : status;
}

int ht_unify(HolTermStore *s, HTerm left, HTerm right)
{
    if (!operation_begin(s)) {
        return -1;
    }
    int result = -1;
    if (left >= s->count || right >= s->count) {
        fail(s, "Unification references an invalid term");
    } else {
        result = unify_equations(s, left, right, 1, NULL, 0);
    }
    operation_end(s);
    return result;
}

/* Open a previously inspected literal clause prefix. Type annotations can
    * refer to earlier binders. A closed annotation is already instantiated. */
int ht_open_binders(HolTermStore *s, HTerm clause, size_t scope, uint32_t type_binders, HTerm *values, size_t count)
{
    if (!operation_begin(s)) return 0;
    if (count > 32 || (count && !values)) fail(s, "Invalid clause binder prefix");
    for (size_t i = 0; !s->error[0] && i < count; ++i) {
        clause = ht_deref(s, clause);
        if (clause == HT_NONE || NODE(s, clause).tag != HT_APP) { fail(s, "Invalid clause binder"); break; }
        HTerm lambda = ht_deref(s, NODE(s, clause).b);
        if (lambda == HT_NONE || NODE(s, lambda).tag != HT_LAM) { fail(s, "Invalid clause binder"); break; }
        TermNode binder = NODE(s, lambda);
        HTerm type = binder.b;
        if (i && type != HT_NONE && !closed_below(NODE(s, type), 0)) {
            type = instantiate(s, type, values, i, 0);
            if (type == HT_NONE) break;
        }
        values[i] = ht_var_typed(s, scope, (type_binders >> i) & 1, binder.meta, type);
        clause = binder.a;
    }
    operation_end(s);
    return !s->error[0];
}

int ht_unify_instance(HolTermStore *s, HTerm goal, HTerm head, const HTerm *values, size_t count)
{
    if (!operation_begin(s)) return -1;
    int valid = goal < s->count && head < s->count && values;
    for (size_t i = 0; valid && i < count; ++i) {
        valid = values[i] < s->count && (NODE(s, values[i]).tag == HT_VAR || NODE(s, values[i]).tag == HT_NOMINAL);
    }
    if (!valid) fail(s, "Invalid clause-head instantiation");
    int result = valid ? unify_equations(s, goal, head, 1, values, count) : -1;
    operation_end(s);
    return result;
}

int ht_retry(HolTermStore *s)
{
    if (!operation_begin(s)) {
        return -1;
    }
    int result = unify_equations(s, HT_NONE, HT_NONE, 0, NULL, 0);
    operation_end(s);
    return result;
}

/* 1: every variable and nominal of the term is within scope and every loose
    * index is below binders; 0: not so; -1: store error. */
static int assignment_scope(HolTermStore *s, HTerm term, size_t scope, size_t binders)
{
    size_t base = s->frame_count;
    int status = 1;
    for (;;) {
        if (!work_okay(s)) {
            status = -1;
            break;
        }
        term = ht_deref(s, term);
        if (term == HT_NONE) {
            fail(s, "Invalid checked assignment term");
            status = -1;
            break;
        }
        TermNode n = NODE(s, term);
        if (stable(n) && n.open != OPEN_UNKNOWN) {
            status = n.scope <= scope && n.open <= binders;
        } else if (n.tag == HT_APP) {
            if (!enter(s, n.b, binders, 0)) {
                status = -1;
                break;
            }
            term = n.a;
            continue;
        } else if (n.tag == HT_LAM) {
            /* The binder's own type is outside the binder. */
            if (n.b != HT_NONE && !enter(s, n.b, binders, 0)) { status = -1; break; }
            term = n.a;
            ++binders;
            continue;
        } else if (n.tag == HT_VAR || n.tag == HT_NOMINAL) {
            status = n.scope <= scope;
        } else if (n.tag == HT_INDEX) {
            status = n.a < binders;
        }
        if (status != 1 || s->frame_count == base) {
            break;
        }
        Frame frame = s->frames[--s->frame_count];
        term = frame.term;
        binders = frame.level;
    }
    s->frame_count = base;
    return status;
}

int ht_assign_checked(HolTermStore *s, HTerm variable, HTerm value)
{
    if (!operation_begin(s)) {
        return -1;
    }
    HTCheckpoint checkpoint = ht_checkpoint(s);
    uint64_t changes = s->changes;
    int status = -1;
    if (variable >= s->count || value >= s->count || NODE(s, variable).tag != HT_VAR) {
        fail(s, "Checked assignment target is not a variable");
    } else {
        HTerm target = ht_deref(s, variable);
        if (NODE(s, target).tag != HT_VAR) {
            status = ht_unify(s, target, value);
        } else {
            value = ht_normalize(s, value, HT_NF);
            if (value != HT_NONE) {
                status = assignment_scope(s, value, NODE(s, target).scope, 0);
                if (status == 1) {
                    status = assign(s, target, value);
                }
                if (status == 1) {
                    status = ht_retry(s);
                }
            }
        }
    }
    if (status != 1) {
        ht_restore(s, checkpoint);
        s->changes = changes;
    }
    operation_end(s);
    return s->error[0] ? -1 : status;
}

size_t ht_pending_count(const HolTermStore *s)
{
    size_t count = 0;
    for (size_t item = s->pending_head; item != HT_NONE; item = s->pending[item].next) {
        ++count;
    }
    return count;
}

int ht_pending(const HolTermStore *s, size_t index, HTerm *left, HTerm *right)
{
    size_t item = s->pending_head;
    while (item != HT_NONE && index) {
        item = s->pending[item].next;
        --index;
    }
    if (item == HT_NONE) {
        return 0;
    }
    *left = s->pending[item].left;
    *right = s->pending[item].right;
    return 1;
}

static int read_word(HolTermStore *s, const int64_t *words, size_t count, size_t *offset, int64_t *value)
{
    if (*offset >= count) {
        return fail(s, "Truncated term wire");
    }
    *value = words[(*offset)++];
    return 1;
}

static HTerm import_identity(HolTermStore *s, int tag, uint64_t uid, size_t scope, int is_type, int64_t meta, HTerm type, int restoring)
{
    HTerm previous = ht_lookup_uid(s, uid);
    if (previous != HT_NONE) {
        TermNode n = NODE(s, previous);
        if (n.tag != tag || n.is_type != is_type || (tag == HT_NOMINAL && n.scope != scope)) {
            fail(s, "Conflicting term identity metadata");
            return HT_NONE;
        }
        if (!s->transient_wire) NODE(s, previous).pinned |= 1;
        return previous;
    }
    if (!restoring && identity_retired(s, uid)) {
        fail(s, "Term wire refers to an expired identity");
        return HT_NONE;
    }
    HTerm created = identity_node(s, tag, uid, scope, is_type, meta, restoring);
    if (created != HT_NONE) {
        NODE(s, created).b = type;
        if (!s->transient_wire) NODE(s, created).pinned |= 1;
    }
    return created;
}

/* One term without subterms; HT_NONE with the store in error. */
static HTerm import_leaf(HolTermStore *s, int64_t tag, const int64_t *words, size_t count, size_t *offset, int restoring)
{
    int64_t a, b, c, d;
    switch (tag) {
        case HT_VAR:
        case HT_NOMINAL: {
            if (!read_word(s, words, count, offset, &a) || !read_word(s, words, count, offset, &b) || !read_word(s, words, count, offset, &c)) {
                return HT_NONE;
            }
            if (tag == HT_VAR) {
                if (!read_word(s, words, count, offset, &d)) {
                    return HT_NONE;
                }
            } else {
                d = c;
                c = 0;
            }
            if (a < 0 || b < 0 || (uint64_t) b > SIZE_MAX || d < -1 || (c != 0 && c != 1)) {
                fail(s, "Invalid variable wire metadata");
                return HT_NONE;
            }
            return import_identity(s, (int) tag, (uint64_t) a, (size_t) b, (int) c, d, HT_NONE, restoring);
        }
        case HT_CONST:
            if (!read_word(s, words, count, offset, &a) || !read_word(s, words, count, offset, &b) || a < 0 || (uint64_t) a > SIZE_MAX || b < -1) {
                fail(s, "Invalid constant wire");
                return HT_NONE;
            }
            return ht_constant(s, (size_t) a, b);
        case HT_INDEX:
            if (!read_word(s, words, count, offset, &a) || a < 0 || (uint64_t) a > SIZE_MAX) {
                fail(s, "Invalid bound variable wire");
                return HT_NONE;
            }
            return ht_index(s, (size_t) a);
        case HT_NAT: {
            if (!read_word(s, words, count, offset, &a) || a <= 0 || (uint64_t) a > count - *offset) {
                fail(s, "Invalid natural wire size");
                return HT_NONE;
            }
            size_t length = (size_t) a;
            char *digits = hm_alloc(s->memory, length + 1);
            if (!digits) {
                fail(s, "Natural wire allocation failed");
                return HT_NONE;
            }
            for (size_t i = 0; i < length; ++i) {
                int64_t digit = words[(*offset)++];
                if (digit < '0' || digit > '9') {
                    hm_free(digits);
                    fail(s, "Invalid natural wire digit");
                    return HT_NONE;
                }
                digits[i] = (char) digit;
            }
            digits[length] = '\0';
            HTerm result = ht_nat(s, digits);
            hm_free(digits);
            return result;
        }
        case HT_WILD:
            return ht_wildcard(s);
        default:
            fail(s, "Invalid term wire tag");
            return HT_NONE;
    }
}

/* Import stages: 0 plain lambda; 1/2 application; 3/4 typed lambda;
    * 5 typed variable; 6 typed nominal. level is metadata plus one. */
static HTerm import_term(HolTermStore *s, const int64_t *words, size_t count, size_t *offset, int restoring)
{
    size_t base = s->frame_count;
    HTerm value = HT_NONE;
    for (;;) {
        int64_t tag, meta;
        if (!work_okay(s) || !read_word(s, words, count, offset, &tag)) break;
        if (tag == HT_APP || tag == HT_LAM || tag == HT_TYPED_LAM) {
            if (!read_word(s, words, count, offset, &meta) || meta < -1) {
                fail(s, "Invalid application or lambda wire");
                break;
            }
            if (!reserve(s, s->frames, &s->frame_capacity, s->frame_count + 1, sizeof(*s->frames))) break;
            unsigned char stage = tag == HT_APP ? 1 : tag == HT_TYPED_LAM ? 3 : 0;
            s->frames[s->frame_count++] = (Frame) { HT_NONE, HT_NONE, (uint64_t) meta + UINT64_C(1), stage, 0 };
            continue;
        }
        if (tag == HT_TYPED_VAR || tag == HT_TYPED_NOMINAL) {
            int64_t uid, scope, is_type = 0;
            if (!read_word(s, words, count, offset, &uid) || !read_word(s, words, count, offset, &scope)
                || (tag == HT_TYPED_VAR && !read_word(s, words, count, offset, &is_type))
                || !read_word(s, words, count, offset, &meta)
                || uid < 0 || scope < 0 || (uint64_t) uid > SIZE_MAX || (uint64_t) scope > SIZE_MAX
                || meta < -1 || (is_type != 0 && is_type != 1)) {
                fail(s, "Invalid typed identity wire");
                break;
            }
            if (!reserve(s, s->frames, &s->frame_capacity, s->frame_count + 1, sizeof(*s->frames))) break;
            s->frames[s->frame_count++] = (Frame) { (HTerm) uid, (HTerm) scope, (uint64_t) meta + UINT64_C(1), tag == HT_TYPED_VAR ? 5 : 6, (unsigned char) is_type };
            continue;
        }
        value = import_leaf(s, tag, words, count, offset, restoring);
        while (value != HT_NONE && s->frame_count > base) {
            Frame frame = s->frames[s->frame_count - 1];
            if (frame.stage == 1 || frame.stage == 3) break;
            --s->frame_count;
            int64_t annotation = frame.level ? (int64_t) (frame.level - UINT64_C(1)) : -1;
            if (frame.stage == 0) value = ht_lam(s, value, annotation);
            else if (frame.stage == 2) value = ht_app(s, frame.term, value, annotation);
            else if (frame.stage == 4) value = ht_lam_typed(s, value, annotation, frame.term);
            else value = import_identity(s, frame.stage == 5 ? HT_VAR : HT_NOMINAL, (uint64_t) frame.term, frame.left, frame.form, annotation, value, restoring);
        }
        if (value == HT_NONE || s->frame_count == base) break;
        s->frames[s->frame_count - 1].term = value;
        ++s->frames[s->frame_count - 1].stage;
        value = HT_NONE;
    }
    s->frame_count = base;
    return s->error[0] ? HT_NONE : value;
}

static HTerm import_wire(HolTermStore *s, const int64_t *words, size_t count, size_t *offset, int restoring)
{
    if (!s || s->error[0] || !offset || *offset > count || (count && !words)) {
        fail(s, "Invalid term wire input");
        return HT_NONE;
    }
    if (!operation_begin(s)) {
        return HT_NONE;
    }
    HTCheckpoint checkpoint = ht_checkpoint(s);
    size_t previous = *offset;
    HTerm term = import_term(s, words, count, offset, restoring);
    if (term == HT_NONE) {
        ht_restore(s, checkpoint);
        *offset = previous;
    }
    operation_end(s);
    return term;
}

HTerm ht_import(HolTermStore *s, const int64_t *words, size_t count, size_t *offset)
{
    return import_wire(s, words, count, offset, 0);
}

HTerm ht_import_restored(HolTermStore *s, const int64_t *words, size_t count, size_t *offset)
{
    return import_wire(s, words, count, offset, 1);
}

/* The wire is the term in prefix order: the frames hold the subterms that
    * are still to be written, the next one on top. */
static int export_term(HolTermStore *s, HTerm root, Words *words)
{
    size_t base = s->frame_count;
    int written = enter(s, root, 0, 0);
    while (written && s->frame_count > base) {
        HTerm term = ht_deref(s, s->frames[--s->frame_count].term);
        if (!work_okay(s)) {
            written = 0;
            break;
        }
        if (term == HT_NONE) {
            written = fail(s, "Invalid term export reference");
            break;
        }
        hm_count(s->memory, HM_NODES_EXPORTED, 1);
        TermNode n = NODE(s, term);
        int tag = n.tag;
        if (n.b != HT_NONE) {
            if (tag == HT_VAR) tag = HT_TYPED_VAR;
            else if (tag == HT_NOMINAL) tag = HT_TYPED_NOMINAL;
            else if (tag == HT_LAM) tag = HT_TYPED_LAM;
        }
        written = push_word(s, words, tag);
        switch (written ? n.tag : -1) {
            case -1:
                break;
            case HT_VAR:
                if (!s->transient_wire) NODE(s, term).pinned |= 1;
                written = push_word(s, words, (int64_t) n.uid) && push_word(s, words, (int64_t) n.scope) && push_word(s, words, n.is_type) && push_word(s, words, n.meta)
                    && (n.b == HT_NONE || enter(s, n.b, 0, 0));
                break;
            case HT_CONST:
                written = push_word(s, words, (int64_t) n.a) && push_word(s, words, n.meta);
                break;
            case HT_APP:
                written = push_word(s, words, n.meta) && enter(s, n.b, 0, 0) && enter(s, n.a, 0, 0);
                break;
            case HT_INDEX:
                written = push_word(s, words, (int64_t) n.a);
                break;
            case HT_LAM:
                written = push_word(s, words, n.meta) && enter(s, n.a, 0, 0)
                    && (n.b == HT_NONE || enter(s, n.b, 0, 0));
                break;
            case HT_NOMINAL:
                if (!s->transient_wire) NODE(s, term).pinned |= 1;
                written = push_word(s, words, (int64_t) n.uid) && push_word(s, words, (int64_t) n.scope) && push_word(s, words, n.meta)
                    && (n.b == HT_NONE || enter(s, n.b, 0, 0));
                break;
            case HT_NAT: {
                size_t length = strlen(n.digits);
                if (length > INT64_MAX || !push_word(s, words, (int64_t) length)) {
                    written = fail(s, "Natural export length overflow");
                }
                for (size_t i = 0; written && i < length; ++i) {
                    written = push_word(s, words, n.digits[i]);
                }
                break;
            }
            case HT_WILD:
                break;
            default:
                written = fail(s, "Invalid term export tag");
                break;
        }
    }
    s->frame_count = base;
    return written;
}

int ht_export_managed(HolTermStore *s, HTerm term, int64_t **words, size_t *count)
{
    if (!words || !count) {
        return fail(s, "Invalid term export buffer");
    }
    *words = NULL;
    *count = 0;
    if (!operation_begin(s)) {
        return 0;
    }
    Words output = { 0 };
    term = ht_normalize(s, term, HT_NF);
    if (term == HT_NONE || !export_term(s, term, &output)) {
        hm_free(output.items);
        operation_end(s);
        return 0;
    }
    *words = output.items;
    *count = output.count;
    operation_end(s);
    return 1;
}

int ht_export_transient(HolTermStore *s, HTerm term, int64_t **words, size_t *count)
{
    HTCheckpoint saved = ht_checkpoint(s);
    int previous = s->transient_wire;
    s->transient_wire = 1;
    int success = ht_export_managed(s, term, words, count);
    s->transient_wire = previous;
    /* The wire owns its words. Normalization creates only structural nodes,
        * never fresh identities; no temporary handle escapes in this wire.
        * Transient normalization reads existing certificates without caching
        * new handles. Reclaim its nodes on failure too, retaining the error
        * and the work counters rather than copying garbage into snapshots. */
    if (!ht_restore(s, saved)) {
        if (success) {
            hm_free(*words);
            *words = NULL;
            *count = 0;
        }
        return 0;
    }
    return success;
}

HTerm ht_import_transient(HolTermStore *s, const int64_t *words, size_t count, size_t *offset)
{
    int previous = s->transient_wire;
    s->transient_wire = 1;
    HTerm term = ht_import(s, words, count, offset);
    s->transient_wire = previous;
    return term;
}

void ht_watch(HolTermStore *s, HTerm term)
{
    if (term < s->count && NODE(s, term).tag == HT_VAR) NODE(s, term).pinned |= 2;
}

HTerm ht_watched_change(const HolTermStore *s, size_t trail)
{
    if (trail >= s->trail_count) return HT_NONE;
    HTerm term = s->trail[trail].variable;
    return (NODE(s, term).pinned & 2) ? term : HT_NONE;
}

/* The public wire retains its historical malloc/free ownership. The machine
    * uses ht_export_managed so its retained wires stay in the native budget. */
int ht_export(HolTermStore *s, HTerm term, int64_t **words, size_t *count)
{
    int64_t *managed = NULL;
    size_t length = 0;
    if (!words || !count) return fail(s, "Invalid term export buffer");
    *words = NULL;
    *count = 0;
    if (!ht_export_managed(s, term, &managed, &length)) return 0;
    size_t bytes = length * sizeof(*managed);
    if (!hm_reserve(s->memory, bytes)) {
        hm_free(managed);
        return fail(s, "Native memory limit exceeded");
    }
    int64_t *plain = malloc(bytes);
    if (plain) memcpy(plain, managed, bytes);
    hm_unreserve(s->memory, bytes);
    hm_free(managed);
    if (!plain) return fail(s, "Term export allocation failed");
    *words = plain;
    *count = length;
    return 1;
}

void ht_pin(HolTermStore *s, HTerm term)
{
    if (s && !s->transient_wire && term >= s->base && term < s->count && !(NODE(s, term).pinned & 1)) {
        if (term - s->base >= FIRST_NODES && !private_page(s, (term - s->base - FIRST_NODES) / PAGE_NODES)) { fail(s, "Term pin page allocation failed"); return; }
        NODE(s, term).pinned |= 1;
    }
}

int ht_mark_query_witness(HolTermStore *s, HTerm term)
{
    if (!s || term < s->base || term >= s->count) return 0;
    TermNode node = NODE(s, term);
    if (node.tag != HT_VAR || node.is_type || node.a != HT_NONE) return 0;
    NODE(s, term).pinned |= 4;
    memo_mutated(s, term);
    return 1;
}

/* The nodes below base are sealed and kept: they are live, stay where they
    * are, and refer to nothing above base. live and forward describe the nodes
    * from base on. */
struct HTCollection {
    HolTermStore *store;
    unsigned char *live;
    size_t *forward, *trail_forward;
    HTerm *stack;
    size_t base, old_heap, old_trail, stack_count, stack_capacity;
    int failed;
};

static int collected_live(const HTCollection *c, HTerm term)
{
    return term < c->base || c->live[term - c->base];
}

/* The new place of a live node, or of a heap position up to the count. */
static size_t collected_at(const HTCollection *c, size_t at)
{
    return at < c->base ? at : c->forward[at - c->base];
}

void ht_collect_mark(HTCollection *c, HTerm term)
{
    HolTermStore *s = c->store;
    size_t base = c->stack_count;
    for (;;) {
        while (term < s->count && !collected_live(c, term)) {
            c->live[term - c->base] = 1;
            hm_count(s->memory, HM_GC_VISITS, 1);
            TermNode n = NODE(s, term);
            if (n.tag == HT_APP || ((n.tag == HT_VAR || n.tag == HT_NOMINAL || n.tag == HT_LAM) && n.b != HT_NONE)) {
                /* Keep a stack entry only when both children still need a visit. */
                term = n.tag == HT_NOMINAL ? HT_NONE : n.a;
                if (term >= s->count || collected_live(c, term)) {
                    term = n.b;
                    continue;
                }
                if (n.b >= s->count || collected_live(c, n.b)) continue;
                if (c->stack_count == c->stack_capacity) {
                    size_t capacity = c->stack_capacity ? c->stack_capacity * 2 : 256;
                    HTerm *grown = capacity > c->stack_capacity && capacity <= SIZE_MAX / sizeof(*grown) ? hm_realloc(c->store->memory, c->stack, capacity * sizeof(*grown)) : NULL;
                    if (!grown) {
                        c->failed = 1;
                        c->stack_count = base;
                        return;
                    }
                    c->stack = grown;
                    c->stack_capacity = capacity;
                }
                c->stack[c->stack_count++] = n.b;
            } else if (n.tag == HT_LAM || n.tag == HT_VAR) {
                term = n.a;
            } else {
                break;
            }
        }
        if (c->stack_count == base) {
            return;
        }
        term = c->stack[--c->stack_count];
    }
}

HTerm ht_collect_term(const HTCollection *c, HTerm term)
{
    return term < c->old_heap && collected_live(c, term) ? collected_at(c, term) : HT_NONE;
}

size_t ht_collect_heap(const HTCollection *c, size_t heap)
{
    return collected_at(c, heap < c->old_heap ? heap : c->old_heap);
}

size_t ht_collect_trail(const HTCollection *c, size_t trail)
{
    return c->trail_forward[trail < c->old_trail ? trail : c->old_trail];
}

static TermNode relocated_node(const HTCollection *c, TermNode n)
{
    if (n.tag == HT_APP) {
        n.a = collected_at(c, n.a);
        n.b = collected_at(c, n.b);
    } else if (n.tag == HT_LAM || n.tag == HT_VAR || n.tag == HT_NOMINAL) {
        if (n.tag != HT_NOMINAL && n.a != HT_NONE) n.a = collected_at(c, n.a);
        if (n.b != HT_NONE) n.b = collected_at(c, n.b);
    }
    return n;
}

/* Even a page before the first hole needs rewriting if a binding or its
    * annotation points forward to a node that moves. */
static int keep_collection_page(const HTCollection *c, size_t i, size_t first_dead)
{
    HolTermStore *s = c->store;
    size_t offset = i - s->base;
    if (offset < FIRST_NODES || offset % PAGE_NODES || i >= first_dead || first_dead - i < PAGE_NODES) return 0;
    TermPage *page = s->arena.pages[(offset - FIRST_NODES) / PAGE_NODES];
    for (size_t j = 0; j < PAGE_NODES; ++j) {
        TermNode n = page->nodes[j], target = relocated_node(c, n);
        if (target.a != n.a || target.b != n.b) return 0;
    }
    return 1;
}

static int prepare_collection_pages(const HTCollection *c, size_t first_dead)
{
    HolTermStore *s = c->store;
    for (size_t i = 0; i < s->arena.count; ++i) {
        TermPage *page = s->arena.pages[i];
        if (atomic_load_explicit(&page->references, memory_order_acquire) != 1
            && keep_collection_page(c, s->base + FIRST_NODES + i * PAGE_NODES, first_dead)) continue;
        if (!private_page(s, i)) return 0;
    }
    return 1;
}

/* A string cell retains its buffer. A natural needs another owned digit
    * allocation, including its allocator header, on either copying path. */
static size_t collection_node_bytes(TermNode n)
{
    return sizeof(TermNode) + (n.tag == HT_NAT ? sizeof(HMemoryHeader) + hm_size(n.digits) : 0);
}

static size_t collection_pages(size_t nodes)
{
    if (nodes <= FIRST_NODES) return 0;
    size_t tail = nodes - FIRST_NODES;
    return tail / PAGE_NODES + (tail % PAGE_NODES != 0);
}

/* Both preparations finish before roots change. Compare the extra charged
    * bytes, not the number of shared pages: a large private live suffix is
    * already writable, while shared pages full of dead naturals are costly
    * to detach. Both costs cover subsets of the already allocated arena. */
static int cheaper_to_rebuild(const HTCollection *c, size_t first_dead, size_t kept)
{
    HolTermStore *s = c->store;
    size_t detach = 0;
    const size_t header = sizeof(HMemoryHeader) + sizeof(TermPage);
    for (size_t i = 0; i < s->arena.count; ++i) {
        TermPage *page = s->arena.pages[i];
        if (atomic_load_explicit(&page->references, memory_order_acquire) == 1) continue;
        if (keep_collection_page(c, s->base + FIRST_NODES + i * PAGE_NODES, first_dead)) continue;
        size_t used = s->count - s->base - FIRST_NODES - i * PAGE_NODES;
        if (used > page->used) used = page->used;
        detach += header;
        for (size_t j = 0; j < used; ++j) detach += collection_node_bytes(page->nodes[j]);
    }
    if (!detach) return 0;
    size_t pages = collection_pages(kept - s->base);
    size_t build = sizeof(HMemoryHeader) + (pages ? sizeof(HMemoryHeader) + pages * sizeof(TermPage *) : 0);
    for (size_t i = s->base; i < s->count && build < detach;) {
        if (keep_collection_page(c, i, first_dead)) {
            i += PAGE_NODES;
            continue;
        }
        if (collected_live(c, i)) {
            size_t dst = collected_at(c, i) - s->base;
            if (dst >= FIRST_NODES && dst % PAGE_NODES == 0) build += header;
            build += collection_node_bytes(NODE(s, i));
        }
        ++i;
    }
    return build < detach;
}

/* The live count is known. Exact capacities give the cost counted above
    * and avoid requesting spare room while the old arena is still alive. */
static int compact_shared(const HTCollection *c, size_t first_dead, TermArena *result)
{
    HolTermStore *s = c->store;
    size_t count = collected_at(c, s->count) - s->base;
    result->first_capacity = count < FIRST_NODES ? count : FIRST_NODES;
    result->first = hm_alloc(s->memory, result->first_capacity * sizeof(*result->first));
    if (!result->first) return fail(s, "Term collection arena allocation failed");
    result->capacity = collection_pages(count);
    if (result->capacity) {
        result->pages = hm_alloc(s->memory, result->capacity * sizeof(*result->pages));
        if (!result->pages) return fail(s, "Term collection page table allocation failed");
    }
    for (size_t i = s->base; i < s->count;) {
        size_t offset = i - s->base;
        if (keep_collection_page(c, i, first_dead)) {
            TermPage *page = s->arena.pages[(offset - FIRST_NODES) / PAGE_NODES];
            atomic_fetch_add_explicit(&page->references, 1, memory_order_relaxed);
            result->pages[result->count++] = page;
            i += PAGE_NODES;
            continue;
        }
        if (collected_live(c, i)) {
            size_t dst = collected_at(c, i) - s->base;
            if (dst >= FIRST_NODES && dst % PAGE_NODES == 0) {
                size_t used = count - dst;
                TermPage *page = new_page(s->memory, used < PAGE_NODES ? used : PAGE_NODES);
                if (!page) return fail(s, "Term collection page allocation failed");
                result->pages[result->count++] = page;
            }
            TermNode n;
            if (!copy_node(s, relocated_node(c, NODE(s, i)), &n)) return fail(s, "Term collection payload allocation failed");
            if (!append_node(s, result, dst, n)) {
                release(n);
                return 0;
            }
        }
        ++i;
    }
    return 1;
}

int ht_collect(HolTermStore *s, size_t keep, const HTCollector *collector, void *context)
{
    if (!s || s->error[0] || s->operations || !collector || keep > s->count) {
        return 0;
    }
    if (keep < s->base && !unshare_prefix(s)) goto skipped;
    memo_release(s);
    HTCollection c = { .store = s, .base = s->sealed < keep ? s->sealed : keep, .old_heap = s->count, .old_trail = s->trail_count };
    size_t span = s->count - c.base;
    c.live = hm_calloc(s->memory, span ? span : 1, 1);
    c.forward = span < SIZE_MAX / sizeof(*c.forward) ? hm_alloc(s->memory, (span + 1) * sizeof(*c.forward)) : NULL;
    c.trail_forward = s->trail_count < SIZE_MAX / sizeof(*c.trail_forward) ? hm_alloc(s->memory, (s->trail_count + 1) * sizeof(*c.trail_forward)) : NULL;
    size_t expired_capacity = s->identity_count, expired_count = 0;
    uint64_t *expired = hm_alloc(s->memory, (expired_capacity ? expired_capacity : 1) * sizeof(*expired));
    int sorted = 1;
    if (!c.live || !c.forward || !c.trail_forward || !expired) {
        c.failed = 1;
    }
    for (size_t i = c.base; !c.failed && i < s->count; ++i) {
        if (i < keep || (NODE(s, i).pinned & 1)) {
            ht_collect_mark(&c, i);
        }
    }
    for (size_t i = 0; !c.failed && i < s->pending_count; ++i) {
        ht_collect_mark(&c, s->pending[i].left);
        ht_collect_mark(&c, s->pending[i].right);
    }
    if (!c.failed && collector->mark) {
        collector->mark(&c, context);
    }
    /* A binding is undone only for a variable that some root still reaches. */
    for (int changed = 1; !c.failed && changed;) {
        changed = 0;
        for (size_t i = 0; !c.failed && i < s->trail_count; ++i) {
            HTerm binding = s->trail[i].binding;
            if (collected_live(&c, s->trail[i].variable) && binding != HT_NONE && !collected_live(&c, binding)) {
                ht_collect_mark(&c, binding);
                changed = 1;
            }
        }
    }
    size_t kept = c.base, first_dead = s->count;
    TermArena compact = { 0 };
    int rebuild = 0, moved = 0;
    if (!c.failed) {
        for (size_t i = 0; i < span; ++i) {
            c.forward[i] = kept;
            if (c.live[i]) ++kept;
            else if (first_dead == s->count) first_dead = c.base + i;
        }
        c.forward[span] = kept;
        moved = first_dead < kept;
        rebuild = moved && cheaper_to_rebuild(&c, first_dead, kept);
        if (rebuild) c.failed = !compact_shared(&c, first_dead, &compact);
        else if (moved) c.failed = !prepare_collection_pages(&c, first_dead);
    }
    if (c.failed) {
        release_arena(&compact);
        hm_free(c.live);
        hm_free(c.forward);
        hm_free(c.trail_forward);
        hm_free(c.stack);
        hm_free(expired);
        goto skipped;
    }
    size_t entries = 0;
    for (size_t i = 0; i < s->trail_count; ++i) {
        c.trail_forward[i] = entries;
        entries += collected_live(&c, s->trail[i].variable);
    }
    c.trail_forward[s->trail_count] = entries;
    for (size_t i = moved ? c.base : first_dead; i < s->count; ++i) {
        TermNode n = NODE(s, i);
        if (!c.live[i - c.base]) {
            if ((n.tag == HT_VAR || n.tag == HT_NOMINAL) && expired_count < expired_capacity) {
                sorted = sorted && (!expired_count || expired[expired_count - 1] < n.uid);
                expired[expired_count++] = n.uid;
                remove_identity(s, n.uid, 0);
            }
            if (moved && !rebuild) release(n);
            continue;
        }
        if (!moved || rebuild) continue;
        TermNode relocated = relocated_node(&c, n);
        /* Unchanged nodes before the first hole may still be shared. */
        if (i < first_dead && relocated.a == n.a && relocated.b == n.b) continue;
        n = relocated;
        size_t target = c.forward[i - c.base];
        NODE(s, target) = n;
        if (target - s->base >= FIRST_NODES && (n.tag == HT_VAR || n.tag == HT_NOMINAL)) {
            s->arena.pages[(target - s->base - FIRST_NODES) / PAGE_NODES]->identities = 1;
        }
    }
    if (!sorted) {
        qsort(expired, expired_count, sizeof(*expired), ascending);
    }
    retire_sorted_from(s, expired, expired_count, sizeof(*expired));
    hm_free(expired);
    for (size_t i = 0; i < s->identity_capacity; ++i) {
        if (s->identities[i].uid != UID_EMPTY) {
            s->identities[i].term = collected_at(&c, s->identities[i].term);
        }
    }
    for (size_t i = 0; i < s->trail_count; ++i) {
        Trail entry = s->trail[i];
        if (collected_live(&c, entry.variable)) {
            entry.variable = collected_at(&c, entry.variable);
            entry.binding = entry.binding == HT_NONE ? HT_NONE : collected_at(&c, entry.binding);
            s->trail[c.trail_forward[i]] = entry;
        }
    }
    for (size_t i = 0; i < s->pending_count; ++i) {
        s->pending[i].left = collected_at(&c, s->pending[i].left);
        s->pending[i].right = collected_at(&c, s->pending[i].right);
    }
    if (rebuild) {
        release_arena(&s->arena);
        s->arena = compact;
    } else if (kept < s->count) {
        truncate_arena(&s->arena, kept - s->base, moved);
    }
    s->count = kept;
    s->trail_count = entries;
    s->sealed = c.base;
    if (collector->relocate) {
        collector->relocate(&c, context);
    }
    /* The table keeps the size that the identities needed since the previous
        * collection: a run that creates as many again does not grow it again. */
    size_t peak = s->identity_peak;
    s->identity_peak = s->identity_count;
    if (s->identity_capacity / 8 > peak && s->identity_capacity > 64) {
        size_t capacity = 64;
        while (capacity / 4 < peak) {
            capacity *= 2;
        }
        rehash_identities(s, capacity);
    }
    hm_free(c.live);
    hm_free(c.forward);
    hm_free(c.trail_forward);
    hm_free(c.stack);
    return 1;

skipped:
    /* Collection is optional. The machine reads the allocator fault to
        * distinguish a memory cap from a failed scratch allocation. */
    if (s->error_code == HT_ERROR_MEMORY || s->error_code == HT_ERROR_ALLOCATION) {
        s->error_code = HT_ERROR_NONE;
        s->error[0] = '\0';
    }
    return 0;
}

/* A snapshot owns exactly its live arena. Geometric spare capacity belongs
    * to a later mutation, not to every retained copy of the same state. */
static void *clone_storage(HolTermStore *store, size_t count, size_t width)
{
    if (!count) return NULL;
    if (count > SIZE_MAX / width) { fail(store, "Term clone size overflow"); return NULL; }
    void *result = hm_alloc(store->memory, count * width);
    if (!result) fail(store, "Term clone allocation failed");
    return result;
}

HolTermStore *ht_clone_in(const HolTermStore *source, HMemory *memory, int legacy)
{
    if (!source) {
        return NULL;
    }
    HolTermStore *copy = ht_create_in(memory);
    if (!copy) {
        return NULL;
    }
    copy->next_uid = source->next_uid;
    copy->successor = source->successor;
    copy->arrow = source->arrow;
    copy->sealed = source->sealed;
    copy->work_limit = source->work_limit;
    if (source->mark_count) {
        if (!reserve(copy, copy->marks, &copy->mark_capacity, source->mark_count, sizeof(*copy->marks))) {
            ht_destroy(copy);
            return NULL;
        }
        memcpy(copy->marks, source->marks, source->mark_count);
        copy->mark_count = source->mark_count;
    }
    copy->changes = source->changes;
    copy->binding_has_loose_indices = source->binding_has_loose_indices;
    copy->prefix = source->prefix;
    copy->base = source->base;
    copy->count = source->base;
    if (copy->prefix) atomic_fetch_add_explicit(&copy->prefix->references, 1, memory_order_relaxed);
    if (memory == source->memory) {
        copy->prefix_lease = source->prefix_lease;
        hm_lease_retain(copy->prefix_lease);
    } else if (copy->prefix) {
        copy->prefix_lease = hm_lease(memory, copy->prefix->bytes);
        if (!copy->prefix_lease) { ht_destroy(copy); return NULL; }
    }
    copy->arena.first_capacity = source->arena.first_used;
    copy->arena.first = clone_storage(copy, copy->arena.first_capacity, sizeof(*copy->arena.first));
    if (copy->arena.first_capacity && !copy->arena.first) { ht_destroy(copy); return NULL; }
    for (size_t i = 0; i < source->arena.first_used; ++i) {
        TermNode value = source->arena.first[i];
        if (!copy_node(copy, value, &copy->arena.first[i])) { ht_destroy(copy); return NULL; }
        ++copy->arena.first_used;
        if ((value.tag == HT_VAR || value.tag == HT_NOMINAL) && !insert_identity(copy, value.uid, copy->count, 1)) {
            ht_destroy(copy);
            return NULL;
        }
        ++copy->count;
    }
    size_t pages = source->arena.count;
    copy->arena.pages = clone_storage(copy, pages, sizeof(*copy->arena.pages));
    if (pages && !copy->arena.pages) { ht_destroy(copy); return NULL; }
    copy->arena.capacity = pages;
    copy->trail_capacity = source->trail_count;
    copy->pending_capacity = source->pending_count;
    copy->trail = clone_storage(copy, copy->trail_capacity, sizeof(*copy->trail));
    if (copy->trail_capacity && !copy->trail) { ht_destroy(copy); return NULL; }
    copy->pending = clone_storage(copy, copy->pending_capacity, sizeof(*copy->pending));
    if (copy->pending_capacity && !copy->pending) { ht_destroy(copy); return NULL; }
    for (size_t number = 0; number < pages; ++number) {
        TermPage *page = source->arena.pages[number];
        size_t used = source->count - copy->count;
        if (used > PAGE_NODES) used = PAGE_NODES;
        if (!legacy && memory == source->memory && !page->identities) {
            atomic_fetch_add_explicit(&page->references, 1, memory_order_relaxed);
        } else {
            page = copy_page(copy, page, used, used);
            if (!page) { ht_destroy(copy); return NULL; }
        }
        copy->arena.pages[copy->arena.count++] = page;
        if (page->identities) {
            for (size_t n = 0; n < used; ++n) {
                TermNode value = page->nodes[n];
                if ((value.tag == HT_VAR || value.tag == HT_NOMINAL) && !insert_identity(copy, value.uid, copy->count + n, 1)) {
                    ht_destroy(copy);
                    return NULL;
                }
            }
        }
        copy->count += used;
    }
    if (source->retired_count) {
        if (!reserve_retired(copy, source->retired_count)) {
            ht_destroy(copy);
            return NULL;
        }
        memcpy(copy->retired, source->retired, source->retired_count * sizeof(*copy->retired));
        copy->retired_count = source->retired_count;
    }
    if (source->trail_count) {
        memcpy(copy->trail, source->trail, source->trail_count * sizeof(*copy->trail));
    }
    if (source->pending_count) {
        memcpy(copy->pending, source->pending, source->pending_count * sizeof(*copy->pending));
    }
    copy->trail_count = source->trail_count;
    copy->pending_count = source->pending_count;
    copy->pending_head = source->pending_head;
    copy->error_code = source->error_code;
    memcpy(copy->error, source->error, sizeof(copy->error));
    if (legacy && !unshare_prefix(copy)) { ht_destroy(copy); return NULL; }
    return copy;
}

HolTermStore *ht_clone(const HolTermStore *source)
{
    return ht_clone_mode(source, 0);
}

HolTermStore *ht_clone_mode(const HolTermStore *source, int legacy)
{
    return source ? ht_clone_in(source, source->memory, legacy) : NULL;
}

/* Reachability for a scoped debugger view. Its table grows with reached nodes,
    * not the heap. Visit raw identities before following their bindings, and
    * include exact type edges, which may themselves contain variables. */
typedef struct { HTerm term; unsigned flags; } ReachEntry;
typedef struct { ReachEntry *entries; size_t capacity, used; } ReachTable;

static ReachEntry *reach_entry(HolTermStore *s, ReachTable *table, HTerm term)
{
    if (!table->capacity || table->used >= table->capacity / 2) {
        size_t next = table->capacity ? table->capacity * 2 : 64;
        if (next < table->capacity || next > SIZE_MAX / sizeof(*table->entries)) {
            fail(s, "Scoped term table overflow"); return NULL;
        }
        ReachEntry *entries = hm_alloc(s->memory, next * sizeof(*entries));
        if (!entries) { fail(s, "Scoped term allocation failed"); return NULL; }
        for (size_t i = 0; i < next; ++i) entries[i] = (ReachEntry) { HT_NONE, 0 };
        for (size_t i = 0; i < table->capacity; ++i) if (table->entries[i].term != HT_NONE) {
            ReachEntry old = table->entries[i];
            size_t at = bucket(old.term, next);
            while (entries[at].term != HT_NONE) at = (at + 1) & (next - 1);
            entries[at] = old;
        }
        hm_free(table->entries);
        table->entries = entries;
        table->capacity = next;
    }
    size_t at = bucket(term, table->capacity);
    while (table->entries[at].term != HT_NONE && table->entries[at].term != term) at = (at + 1) & (table->capacity - 1);
    if (table->entries[at].term == HT_NONE) {
        table->entries[at].term = term;
        ++table->used;
    }
    return &table->entries[at];
}

/* A callback needs explicit named root bindings and the open variables in
    * their values, not a separate copy of every already bound internal alias.
    * flags: bit0 has emitted this identity; bit1 has traversed this node. */
static int reachable(HolTermStore *s, const HTerm *roots, size_t count, HTerm **variables, size_t *variable_count, int values)
{
    if (!s || !variables || !variable_count || !operation_begin(s)) return 0;
    Terms pending = { 0 }, found = { 0 };
    ReachTable seen = {0};
    int success = 1;
    *variables = NULL;
    *variable_count = 0;
    for (size_t i = 0; success && i < count; ++i) {
        HTerm root = roots[i];
        if (root == HT_NONE) continue;
        if (root >= s->count) { success = fail(s, "Invalid scoped term reference"); break; }
        TermNode n = NODE(s, root);
        if (values && n.tag == HT_VAR) {
            if (!work_okay(s)) { success = 0; break; }
            ReachEntry *entry = reach_entry(s, &seen, root);
            if (!entry) { success = 0; break; }
            if (!(entry->flags & 1)) {
                entry->flags |= 1;
                success = push_term(s, &found, root);
                if (success && n.b != HT_NONE) success = push_term(s, &pending, n.b);
            }
        }
        if (success) success = push_term(s, &pending, root);
    }
    while (success && pending.count) {
        HTerm term = pending.items[--pending.count];
        if (values) term = ht_deref(s, term);
        if (term >= s->count) { success = fail(s, "Invalid scoped term reference"); break; }
        if (!work_okay(s)) { success = 0; break; }
        ReachEntry *entry = reach_entry(s, &seen, term);
        if (!entry) { success = 0; break; }
        if (entry->flags & 2) continue;
        entry->flags |= 2;
        TermNode n = NODE(s, term);
        if ((n.tag == HT_VAR || n.tag == HT_NOMINAL) && !(entry->flags & 1)) {
            entry->flags |= 1;
            success = push_term(s, &found, term);
        }
        if (success && (n.tag == HT_APP || n.tag == HT_LAM || n.tag == HT_VAR) && n.a != HT_NONE) success = push_term(s, &pending, n.a);
        if (success && (n.tag == HT_APP || n.tag == HT_LAM || n.tag == HT_VAR || n.tag == HT_NOMINAL) && n.b != HT_NONE) success = push_term(s, &pending, n.b);
    }
    hm_free(pending.items);
    hm_free(seen.entries);
    operation_end(s);
    if (!success) { hm_free(found.items); return 0; }
    *variables = found.items;
    *variable_count = found.count;
    return 1;
}

int ht_reachable(HolTermStore *s, const HTerm *roots, size_t count, HTerm **variables, size_t *variable_count)
{
    return reachable(s, roots, count, variables, variable_count, 0);
}

int ht_reachable_values(HolTermStore *s, const HTerm *roots, size_t count, HTerm **variables, size_t *variable_count)
{
    return reachable(s, roots, count, variables, variable_count, 1);
}

int ht_set_initial_type(HolTermStore *s, HTerm variable, HTerm type)
{
    if (!s || !operation_begin(s)) return 0;
    Terms pending = { 0 };
    ReachTable seen = { 0 };
    int success = variable < s->count && type < s->count;
    if (success) {
        TermNode target = NODE(s, variable);
        success = target.tag == HT_VAR && !target.is_type && target.a == HT_NONE && target.b == HT_NONE;
    }
    if (!success) fail(s, "Invalid initial query type target");
    if (success) success = push_term(s, &pending, type);
    while (success && pending.count) {
        HTerm term = pending.items[--pending.count];
        if (term >= s->count || !work_okay(s)) { success = 0; break; }
        ReachEntry *entry = reach_entry(s, &seen, term);
        if (!entry) { success = 0; break; }
        if (entry->flags) continue;
        entry->flags = 1;
        TermNode n = NODE(s, term);
        if (n.tag == HT_APP) success = push_term(s, &pending, n.a) && push_term(s, &pending, n.b);
        else if (n.tag != HT_CONST && !(n.tag == HT_VAR && n.is_type && n.a == HT_NONE && n.b == HT_NONE)) success = fail(s, "Invalid initial query type graph");
    }
    if (success) {
        NODE(s, variable).b = type;
        memo_mutated(s, variable);
    }
    hm_free(pending.items);
    hm_free(seen.entries);
    operation_end(s);
    return success;
}
