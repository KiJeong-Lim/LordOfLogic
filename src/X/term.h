#ifndef HOL_V1_TERM_H
#define HOL_V1_TERM_H

#include <stddef.h>
#include <stdint.h>

#define HT_NONE SIZE_MAX

typedef size_t HTerm;
typedef struct HolTermStore HolTermStore;
typedef struct HMemory HMemory;
enum HTError { HT_ERROR_NONE, HT_ERROR_INTERNAL, HT_ERROR_WORK, HT_ERROR_MEMORY, HT_ERROR_ALLOCATION };

enum HTTag { HT_VAR, HT_CONST, HT_APP, HT_INDEX, HT_LAM, HT_NOMINAL, HT_NAT, HT_WILD };
enum HTWireTag { HT_TYPED_LAM = 8, HT_TYPED_VAR = 9, HT_TYPED_NOMINAL = 10 };
enum HTNormalForm { HT_WHNF, HT_HNF, HT_NF };

/* uid is the identity of a variable or a nominal and digits are those of a
    * natural; neither says anything about a node of another tag. */
typedef struct {
    int tag;
    HTerm a, b;
    uint64_t uid;
    size_t symbol, scope;
    int is_type;
    int64_t meta;
    const char *digits;
} HTView;

typedef struct {
    size_t heap, trail, pending, pending_head;
} HTCheckpoint;

/* A few arguments are kept in the spine itself, so a spine is not copied:
    * args may point into it. */
typedef struct {
    HTerm head;
    HTerm *args;
    size_t count;
    HTerm few[6];
} HTSpine;

HolTermStore *ht_create(void);
HolTermStore *ht_create_in(HMemory *memory);
HMemory *ht_memory(const HolTermStore *store);
int ht_error_code(const HolTermStore *store);
HolTermStore *ht_clone_in(const HolTermStore *source, HMemory *memory, int legacy);
HolTermStore *ht_clone_mode(const HolTermStore *source, int legacy);
HolTermStore *ht_clone(const HolTermStore *source);
void ht_destroy(HolTermStore *store);
const char *ht_error(const HolTermStore *store);
size_t ht_heap_count(const HolTermStore *store);
HTCheckpoint ht_checkpoint(const HolTermStore *store);
int ht_restore(HolTermStore *store, HTCheckpoint checkpoint);
/* The state between two runs: the first heap nodes stay, every binding is
    * undone, no disagreement is pending, and the identities from next_uid on, the
    * marks of the symbols from symbols on and the work limit are forgotten. The
    * caller keeps no node and no identity above those bounds. 0: store error. */
int ht_reset(HolTermStore *store, size_t heap, uint64_t next_uid, size_t symbols);
/* Seals the nodes that precede the first variable: no binding can make them
    * refer to a younger node, so a collection that keeps them neither visits nor
    * moves them. Returns their number; ht_sealed reads it. */
size_t ht_seal(HolTermStore *store);
size_t ht_sealed(const HolTermStore *store);
uint64_t ht_next_uid(const HolTermStore *store);
/* Advancing the fresh-UID frontier does not retire never-materialized gaps. */
int ht_advance_uid(HolTermStore *store, uint64_t next_uid);
/* Preserve retirement when replacing a live store with an older snapshot. */
int ht_preserve_identity_history(HolTermStore *restored, const HolTermStore *live);
/* Same-query consuming restore metadata. Success makes live destruction-only;
    * failure changes neither logical state. May reserve retirement capacity. */
int ht_consume_history(HolTermStore *restored, HolTermStore *live);
/* Symbol role changes return 0 on failure and keep the previous role. */
int ht_set_successor(HolTermStore *store, size_t symbol);
void ht_set_arrow(HolTermStore *store, size_t symbol);
int ht_set_opaque_symbol(HolTermStore *store, size_t symbol);
/* An arithmetic symbol is one that the host evaluates. ht_mentions_arithmetic
    * is 1 when the term, as bound now, contains such a symbol, the successor or
    * an opaque symbol; 0 when it contains none; -1 on a store error. */
int ht_set_arithmetic_symbol(HolTermStore *store, size_t symbol);
int ht_mentions_arithmetic(HolTermStore *store, HTerm term);
/* Positive per-operation node-visit bound; nested operations share the budget. */
/* Marks a constructor of types. The first argument of a wildcard is its type
    * exactly when it is built of such constructors and of type variables. */
int ht_set_type_symbol(HolTermStore *store, size_t symbol);
int ht_set_work_limit(HolTermStore *store, uint64_t visits);
uint64_t ht_work_limit(const HolTermStore *store);

HTerm ht_var(HolTermStore *store, size_t scope, int is_type, int64_t meta);
HTerm ht_nominal(HolTermStore *store, size_t scope, int64_t meta);
HTerm ht_var_typed(HolTermStore *store, size_t scope, int is_type, int64_t meta, HTerm type);
HTerm ht_nominal_typed(HolTermStore *store, size_t scope, int64_t meta, HTerm type);
/* Startup only: attach a simple Hol type to a fresh ordinary query identity.
    * Type edges may contain constants, applications and free type identities.
    * The loader calls this before execution; this is not a trailed edit API. */
int ht_set_initial_type(HolTermStore *store, HTerm variable, HTerm type);
/* Exact type of this raw identity or lambda; never dereferences its value. */
HTerm ht_type(const HolTermStore *store, HTerm term);
HTerm ht_constant(HolTermStore *store, size_t symbol, int64_t meta);
HTerm ht_nat(HolTermStore *store, const char *digits);
HTerm ht_index(HolTermStore *store, size_t index);
HTerm ht_lam(HolTermStore *store, HTerm body, int64_t meta);
HTerm ht_lam_typed(HolTermStore *store, HTerm body, int64_t meta, HTerm type);
HTerm ht_app(HolTermStore *store, HTerm function, HTerm argument, int64_t meta);
HTerm ht_wildcard(HolTermStore *store);
/* The contents of a string literal: the symbols of its constructor, of its
    * nil and of their type argument, and those of its count >= 1 elements. The
    * caller owns the reference it gets and gives it back with ht_string_release;
    * every cell keeps one of its own. NULL: store error. */
typedef struct HTStringBuffer HTStringBuffer;
HTStringBuffer *ht_string_buffer(HolTermStore *store, size_t cons, size_t nil, size_t type, const int64_t *symbols, size_t count);
void ht_string_release(HTStringBuffer *buffer);
/* The cell of the element at offset: the application of function, which is
    * `cons type` applied to that element, to tail, which is the cell at offset
    * + 1 or `nil type` after the last element. It is the term that ht_app
    * builds, and it is compared with another cell through the buffers. A
    * function or a tail of any other shape is a store error. */
HTerm ht_string_cell(HolTermStore *store, HTerm function, HTerm tail, int64_t meta, HTStringBuffer *buffer, size_t offset);
HTerm ht_lookup_uid(const HolTermStore *store, uint64_t uid);
HTerm ht_deref(const HolTermStore *store, HTerm term);
HTView ht_view(const HolTermStore *store, HTerm term);
int ht_reachable(HolTermStore *store, const HTerm *roots, size_t count, HTerm **variables, size_t *variable_count);
/* Explicit raw-variable roots plus open identities in dereferenced values and
    * their exact types; omits already bound internal aliases. */
int ht_reachable_values(HolTermStore *store, const HTerm *roots, size_t count, HTerm **variables, size_t *variable_count);
int ht_same(HolTermStore *store, HTerm left, HTerm right);
HTerm ht_normalize(HolTermStore *store, HTerm term, enum HTNormalForm form);
HTerm ht_apply(HolTermStore *store, HTerm function, HTerm argument);
/* Replaces the indices of count enclosing binders at once: index i of body
    * denotes values[count - 1 - i]. Every value is a variable or a nominal. */
HTerm ht_instantiate(HolTermStore *store, HTerm body, const HTerm *values, size_t count);
int ht_spine(HolTermStore *store, HTerm term, HTSpine *spine);
void ht_spine_free(HTSpine *spine);

/* Unification is atomic on logical failure and preserves unresolved equations.
    * -1: store error; 0: incompatible terms; 1: solved or retained disagreement. */
int ht_open_binders(HolTermStore *store, HTerm clause, size_t scope, uint32_t type_binders, HTerm *values, size_t count);
int ht_unify_instance(HolTermStore *store, HTerm goal, HTerm head, const HTerm *values, size_t count);
int ht_unify(HolTermStore *store, HTerm left, HTerm right);
int ht_retry(HolTermStore *store);
/* Host type-checked debugger assignment: strict scope/occurs checks, permitting
    * opaque goal values. Existing bindings are checked by ordinary unification. */
int ht_assign_checked(HolTermStore *store, HTerm variable, HTerm value);
size_t ht_pending_count(const HolTermStore *store);
int ht_pending(const HolTermStore *store, size_t index, HTerm *left, HTerm *right);

/* Prefix term wire, matching HTTag. VAR: uid,scope,is_type,meta;
    * CONST: symbol,meta; APP: meta,fn,arg; INDEX: index; LAM: meta,body;
    * NOMINAL: uid,scope,meta; NAT: byte-count,decimal ASCII; WILD: no payload.
    * Typed extensions: 8=LAM(meta,type,body), 9=VAR(uid,scope,is_type,meta,type),
    * 10=NOMINAL(uid,scope,meta,type). Existing identities retain their own type.
    * Import consumes one term, advances *offset, and reuses live UID identities.
    * Export allocates *words; caller releases it with free(). */
/* Export and import pin the identities they name: the host may name a pinned
    * variable or nominal again, so a collection keeps it. */
HTerm ht_import(HolTermStore *store, const int64_t *words, size_t count, size_t *offset);
/* Authorized snapshot/persistent-assignment replay may restore retired UIDs. */
HTerm ht_import_restored(HolTermStore *store, const int64_t *words, size_t count, size_t *offset);
int ht_export(HolTermStore *store, HTerm term, int64_t **words, size_t *count);
/* Internal native ownership: release with hm_free (native_memory.h). */
int ht_export_managed(HolTermStore *store, HTerm term, int64_t **words, size_t *count);
/* Service wires are borrowed by the host until their registered token dies;
    * they do not acquire the permanent debugger pin. */
int ht_export_transient(HolTermStore *store, HTerm term, int64_t **words, size_t *count);
HTerm ht_import_transient(HolTermStore *store, const int64_t *words, size_t count, size_t *offset);
void ht_watch(HolTermStore *store, HTerm term);
HTerm ht_watched_change(const HolTermStore *store, size_t trail);

void ht_pin(HolTermStore *store, HTerm term);
/* Legacy terminal display only: preserve the original query variable's first
    * existential representative. This is not a pin or a typing annotation. */
int ht_mark_query_witness(HolTermStore *store, HTerm term);

/* Order-preserving compaction. The first keep nodes, pinned identities, every
    * disagreement and whatever mark names stay; a trailed binding stays with its
    * variable. The cost does not depend on the sealed nodes among the first
    * keep. During relocate the maps accept old terms and checkpoint positions;
    * the store can already be read at their new positions. Unreachable
    * identities are retired. A temporary allocation failure returns 0 and
    * leaves the logical state and the caller's roots available for retry. */
typedef struct HTCollection HTCollection;
typedef struct {
    void (*mark)(HTCollection *collection, void *context);
    void (*relocate)(const HTCollection *collection, void *context);
} HTCollector;
void ht_collect_mark(HTCollection *collection, HTerm term);
HTerm ht_collect_term(const HTCollection *collection, HTerm term);
size_t ht_collect_heap(const HTCollection *collection, size_t heap);
size_t ht_collect_trail(const HTCollection *collection, size_t trail);
int ht_collect(HolTermStore *store, size_t keep, const HTCollector *collector, void *context);

#endif
