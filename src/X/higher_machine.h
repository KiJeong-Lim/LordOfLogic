#ifndef HOL_V2_MACHINE_H
#define HOL_V2_MACHINE_H

#include <stddef.h>
#include <stdint.h>

typedef struct HolV2Machine HolV2Machine;

enum HolV2Error {
    HV2_ERROR_NONE, HV2_ERROR_USAGE, HV2_ERROR_WORK,
    HV2_ERROR_MEMORY, HV2_ERROR_ALLOCATION, HV2_ERROR_INTERNAL,
    HV2_ERROR_INVALID_GOAL, HV2_ERROR_INVALID_FACT
};
#define HV2_STATS_COUNT 14
void hol_v2_set_legacy_copy(HolV2Machine *machine, int enabled);
/* Scoped views borrow identities from live goals, registered host roots and
    * snapshots. Observing a view does not permanently pin its local handles. */
void hol_v2_set_scoped_exports(HolV2Machine *machine, int enabled);
/* Original named query slots of a legacy terminal. Validation is atomic;
    * public scoped runs cannot enable this display compatibility policy. */
int hol_v2_set_query_witnesses(HolV2Machine *machine, const uint64_t *slots, size_t count);
/* Zero means no native limit. The account includes this run's snapshots;
    * restoring a snapshot never restores an older limit. */
int hol_v2_set_memory_limit(HolV2Machine *machine, uint64_t bytes);
uint64_t hol_v2_memory_limit(const HolV2Machine *machine);
int hol_v2_error_code(const HolV2Machine *machine);
/* A typed logical error owns a one-root wire captured before the run stops.
    * Reading it does not resume or clear the failed state. */
size_t hol_v2_failure_size(const HolV2Machine *machine);
int hol_v2_failure(const HolV2Machine *machine, int64_t *output, size_t capacity);
void hol_v2_set_counting(HolV2Machine *machine, int enabled);
/* bytes, peak bytes, heap nodes, sealed nodes, collections; then cumulative
    * visits, normalization, binding, scope, created, copied, exported, GC,
    * copied program-table rows (including initial appends and index paths).
    * Visit counting is opt-in; memory accounting is always enabled. */
int hol_v2_stats(const HolV2Machine *machine, uint64_t *values, size_t count);

/* General wordcode header[8]: magic=0x484f4c31, version=2 through 6, term count,
    * symbol count, fact count, query-slot count, query term root, metadata count.
    * Sections follow in this order:
    *   query slots: is_type, metadata (-1 means absent); v5 and v6 add type root
    *   symbols[1]: role (enum HolV2Role)
    *   templates[6]: tag,a,b,c,d,metadata; unused operands are zero
    *   facts[2]: predicate symbol (-1 means inspect dynamically), template root
    *   remaining words: literal payload, addressed relative to its start.
    * Template tags: 0=query VAR(a=slot), 1=CONST(a=symbol), 2=APP(a=fn,b=arg),
    * 3=INDEX(a=index), 4=LAM(a=body), 5=NAT(a=payload offset,b=length), 6=WILD.
    * Version 3 also has 7=STRING(a=typed cons,b=typed nil,c=payload offset,
    * d=character count). Its payload contains ordinary symbol IDs, and it
    * builds an ordinary list with the occurrence's metadata on each character
    * and new application. When a and b are an ordinary constant applied to one
    * ordinary constant, the same for both, the cells of the list are string
    * cells (term.h). NAT payload entries remain decimal ASCII words.
    * Version 4 adds an optional lambda type: LAM b=type-template+1, or 0
    * when absent. That type is in the context outside the lambda binder.
    * Version 5 adds a query-slot type root (-1 means absent). Type-only slots
    * have no term type. Edges are installed after all slots and templates exist.
    * Version 6 marks ordinary type constructors with role HV2_TYPE.
    * Child templates precede their parents. Every goal executes as native EXEC
    * over its compiled term graph; clauses retain their quantifier/lambda nodes.
    */
enum HolV2Role {
    HV2_ORDINARY, HV2_TY_PI, HV2_IF, HV2_TRUE, HV2_FAIL, HV2_CUT,
    HV2_AND, HV2_OR, HV2_IMPLY, HV2_PI, HV2_SIGMA, HV2_DEBUG,
    HV2_IS, HV2_EQ, HV2_LE, HV2_LT, HV2_GE, HV2_GT,
    HV2_READ, HV2_PRINT, HV2_PRESBURGER, HV2_SUCCESSOR, HV2_FLEX,
    HV2_ARITHMETIC, HV2_NATURAL, HV2_ORACLE, HV2_ARROW, HV2_SAME, HV2_TYPE
};
/* HV2_FLEX is decided by the machine itself: `flex T` succeeds exactly when the
    * head of T, below its leading abstractions and after dereferencing, is an
    * unbound variable. It binds nothing and raises no host event.
    * HV2_ARITHMETIC marks a function that the host evaluates (+, -, *, /),
    * HV2_NATURAL the type of naturals, HV2_ARROW the type of functions and
    * HV2_TYPE every other constructor of types. They are ordinary constants to
    * the search; the last three tell the term store what a type is.
    * An equality whose type is not HV2_NATURAL and whose sides, as bound now,
    * contain no HV2_ARITHMETIC, HV2_SUCCESSOR or HV2_PRESBURGER symbol raises no
    * host event: the host would answer "unknown" (4) without reading a state.
    * An implication whose antecedent is a conjunction of atoms and clauses with
    * ordinary heads raises none either: the host would add no premise.
    * HV2_ORACLE is `oracle Name Term`: a primitive event, as HV2_READ and
    * HV2_PRINT are; the host answers it, and may read the hypotheses of the
    * goal (hol_v2_hypotheses). */

enum HolV2Event {
    HV2_EVENT_PRIMITIVE = 1,
    HV2_EVENT_SETTLE = 2,
    HV2_EVENT_IMPLY = 3,
    HV2_EVENT_DEBUG = 4,
    HV2_EVENT_EQUALITY = 5,
    HV2_EVENT_STEP_FAILED = 6
};

HolV2Machine *hol_v2_create_limited(const int64_t *code, size_t length, uint64_t limit, int *error_code);
HolV2Machine *hol_v2_create(const int64_t *code, size_t length);
/* A machine keeps its program across runs. A fragment is wordcode whose symbol
    * count is the total after it and whose symbol section lists the roles of the
    * symbols the machine does not have yet; its templates, clauses and digits
    * are its own, numbered from zero. Versions 2, 3, 4 and 5 may be mixed.
    *   extend: no query slot, query root -1. Its symbols and clauses join the
    *     program, after the ones already there.
    *   query: no clause. Its symbols and its query last for one run.
    *   idle: leaves the run and releases what it allocated.
    * A successful nonempty extension and query leave the current run first.
    * Extension is staged: rejection preserves program, run and snapshots.
    * Empty extension preserves the run and program version too. After leaving a run the
    * machine numbers variables, calls and host states as the created machine
    * did, and no snapshot of that run can be restored. 1, or -1 with an API
    * error for rejected extension and an execution error for a failed query. */
int hol_v2_extend(HolV2Machine *machine, const int64_t *code, size_t length);
int hol_v2_query(HolV2Machine *machine, const int64_t *code, size_t length);
int hol_v2_idle(HolV2Machine *machine);
void hol_v2_destroy(HolV2Machine *machine);
const char *hol_v2_error(const HolV2Machine *machine);
/* -1 error, 0 exhausted, 1 answer, 2 cancellation yield, 3 host service.
    * Clause trials and failed-choice traversal share the scheduler budget;
    * a yielded search can be cloned/restored before the next call. */
/* As next, optionally setting the debugger flag (-1 preserves it). An answer
    * returns its host token in word 0. A request writes its six info words, its
    * payload size, and the payload if it fits; otherwise use hol_v2_event.
    * The caller supplies at least seven words. */
int hol_v2_next_event(HolV2Machine *machine, int debugging, int64_t *output, size_t capacity);
int hol_v2_next(HolV2Machine *machine);

/* A proof step fences alternatives already present when it begins. Failure
    * raises STEP_FAILED before restoring any of them, or before exhaustion.
    * Alternatives created in the step are still tried. The failure event is
    * sticky: end_step with the same ID explicitly permits the older search;
    * restoring a snapshot restores its own boundary instead. IDs are positive
    * and at most INT64_MAX. Only one boundary may be active. These APIs do not
    * poison the machine on an invalid request. */
int hol_v2_begin_step(HolV2Machine *machine, uint64_t step_id);
int hol_v2_end_step(HolV2Machine *machine, uint64_t step_id);

/* Buffers are owned by the machine until its next mutating API call.
    * Call size then copy. Copy returns -1 on invalid capacity, otherwise 1.
    * Query answer: [query-count, term-wire...]. All term-wire uses term.h tags.
    * State: [variable-count, raw-VAR-wire, dereferenced-value-wire, ...,
    *         disagreement-count, lhs-wire, rhs-wire, ...].
    * Event terms: [root-count, term-wire...]; one goal/antecedent root normally,
    * zero roots for SETTLE. Event info[6] is kind, host-state-token,
    * premise-token, scope, call-id, auxiliary. SETTLE auxiliary=1 at answer.
    * STEP_FAILED has no roots and auxiliary=step ID; its other metadata is
    * zero. Its transient failed branch must not be exported as a proof state.
    */
size_t hol_v2_answer_size(HolV2Machine *machine);
int hol_v2_answer(HolV2Machine *machine, int64_t *output, size_t capacity);
/* Full callback view includes query slots. Proof view contains current and
    * continuation goals/hypotheses plus explicit host roots and exact types;
    * it neither exports nor pins an unrelated query result. Both use state(). */
size_t hol_v2_view_state_size_with(HolV2Machine *machine, const uint64_t *uids, size_t count);
size_t hol_v2_proof_state_size_with(HolV2Machine *machine, const uint64_t *uids, size_t count);
/* Assignment metadata for the full view's same identity closure. [0] requests
    * the legacy occurrence-order view; [1, count, raw-identity-wires...] is
    * available only when every value identity has an exact closed type.
    * An unavailable supplied UID requests fallback without poisoning the run.
    * Bindings and disagreements still come from view_state_size_with(). */
size_t hol_v2_assignment_declarations_size_with(HolV2Machine *machine, const uint64_t *uids, size_t count);
size_t hol_v2_view_state_size(HolV2Machine *machine);
size_t hol_v2_live_tokens_size(HolV2Machine *machine);
size_t hol_v2_live_views_size(HolV2Machine *machine);
size_t hol_v2_live_identities_size(HolV2Machine *machine);
/* Drain [count, kind, token,...], kind0 constraint state, kind1 view base.
    * Last-current/choice-reference retirement requires no arena scan. */
size_t hol_v2_retired_tokens_size(HolV2Machine *machine);
/* Immutable base-view token followed by the ordinary state layout, restricted
    * to watched changes since that base and this request's normalized roots.
    * No deletion is needed: checkpoint restoration restores the base token too.
    * Copy with hol_v2_state. Host root sets are immutable per kind/token;
    * kind 0 is a constraint token, kind 1 an arithmetic premise token. */
size_t hol_v2_service_delta_size(HolV2Machine *machine);
int hol_v2_register_host_roots(HolV2Machine *machine, int kind, uint64_t token, const uint64_t *uids, size_t count);
size_t hol_v2_state_size(HolV2Machine *machine);
int hol_v2_state(HolV2Machine *machine, int64_t *output, size_t capacity);
/* Root state: the State layout restricted to the query slots (with_query) or
    * to no variable at all, followed by every disagreement. Copy it with
    * hol_v2_state. It suffices while the host holds no constraint or premise. */
size_t hol_v2_root_state_size(HolV2Machine *machine, int with_query);
size_t hol_v2_pending_count(const HolV2Machine *machine);
/* Every identity created so far is below this bound. */
uint64_t hol_v2_uid_frontier(const HolV2Machine *machine);
/* The raw wire of a live identity, without dereferencing or pinning it.
    * Returns 5 (VAR), 4 (NOMINAL), or -1 with the machine in error. A host
    * reconstructing an earlier identity must not turn a missing one into a
    * freshly reserved variable. This lookup uses the existing expiry error. */
int hol_v2_identity(HolV2Machine *machine, uint64_t uid, int64_t *output, size_t capacity);
size_t hol_v2_event_size(HolV2Machine *machine);
int hol_v2_event(HolV2Machine *machine, int64_t *output, size_t capacity);
int hol_v2_event_info(const HolV2Machine *machine, int64_t *output, size_t capacity);
uint64_t hol_v2_host_state(const HolV2Machine *machine);

size_t hol_v2_frames_size(HolV2Machine *machine);
/* Legacy frame wire, or [-2, frame-count, frames...]. A compact frame begins
    * with scope/call, then a hypothesis chain: 1/id/fact introduces a node,
    * 0 ends the chain, and 2/id reuses a previously completed suffix. The
    * frame's goal follows. A term's 11/id/wire defines an exact subtree;
    * 12/id references a completed definition. Term IDs and hypothesis IDs
    * are separate dictionaries, both limited to this buffer. A view with
    * lexical type quantifiers, metadata-dependent identities, or annotations
    * other than closed CONST/APP type trees uses the legacy format. */
size_t hol_v2_compact_frames_size(HolV2Machine *machine);
/* A debugger host that reads only some hypotheses of the current goal names
    * their predicates. Its debugger views (hol_v2_proof_state_size_with and
    * hol_v2_proof_frames_size) then have the current goal alone and, of its
    * hypotheses, those of the named predicates and those whose predicate is
    * not known. Every other view is complete. */
int hol_v2_set_debug_focus(HolV2Machine *machine, const uint64_t *symbols, size_t count, int enabled);
size_t hol_v2_proof_frames_size(HolV2Machine *machine);
int hol_v2_frames(HolV2Machine *machine, int64_t *output, size_t capacity);
/* Compact metadata from pending frames: [count, raw VAR/NOMINAL wires...].
    * Preserves all occurrences in frame traversal order: repeated type-binder
    * declarations can affect the metadata of later variables and nominals. */
size_t hol_v2_declarations_size(HolV2Machine *machine);
int hol_v2_declarations(HolV2Machine *machine, int64_t *output, size_t capacity);
/* Where the goal of the event stands: [scope, hypothesis-count,
    * term-wire...]. The scope is the number of `pi` around the goal, and the
    * hypotheses are those that `=>` has given it, the latest first.
    * An idle machine reports [0, 0]. */
size_t hol_v2_hypotheses_size(HolV2Machine *machine);
int hol_v2_hypotheses(HolV2Machine *machine, int64_t *output, size_t capacity);

/* Bindings: [count, lhs-term-wire, rhs-term-wire, ...]. result=0 rejects this branch;
    * 1 continues. For EQUALITY use 2=true, 3=false, 4=unknown (after definitions);
    * matching local hypotheses take precedence over that result.
    * IMPLY returns a lexical premise token; other events retain the old token.
    * host state tokens are immutable host-owned values saved in choice points.
    * Equality responses schedule clause search; search errors are reported by next.
    */
int hol_v2_resume(HolV2Machine *machine, int result, uint64_t host_state,
    uint64_t premises, const int64_t *bindings, size_t length);
/* The view is the host's immutable state BEFORE applying these reply bindings.
    * Plain resume preserves the earlier view watermark (notably for debugger
    * assignments). The host owns view IDs and keeps live IDs plus snapshots. */
int hol_v2_resume_with_view(HolV2Machine *machine, int result, uint64_t host_state,
    uint64_t premises, uint64_t view, const int64_t *bindings, size_t length);
/* Atomic resume plus immutable constraint/premise root-set changes. The wire is
    * [entries, kind, token, parent, added-count, added UIDs..., removed-count,
    * removed UIDs..., ...], at most three entries: kind0 constraints, kind1
    * premises, kind4 variable subscription for this view. An absent kind4 keeps
    * historical watches; an empty kind4 emits only event/disagreement roots.
    * Parent0 is empty. Removal precedes addition. Validation errors before resume
    * preserve the pending event; allocation/import/expired added-UID failures
    * interrupt execution and require restoring a snapshot or starting a new run. */
int hol_v2_resume_with_root_deltas(HolV2Machine *machine, int result, uint64_t host_state,
    uint64_t premises, uint64_t view, const int64_t *bindings, size_t length,
    const uint64_t *roots, size_t root_length);
/* Persistent assignments, [count, VAR-wire, value-wire, ...]: each holds from
    * now on wherever its target exists, in the alternatives too. The machine
    * keeps them for the run and makes one again when a backtracking step has
    * undone it; while its binding is there it costs nothing. An assignment
    * that does not hold in the current state fails the branch. A snapshot has
    * the assignments that were given before it was taken. */
int hol_v2_assign(HolV2Machine *machine, const int64_t *bindings, size_t length);
void hol_v2_set_debugging(HolV2Machine *machine, int enabled);
int hol_v2_ensure_symbol(HolV2Machine *machine, size_t symbol, int role);
uint64_t hol_v2_reserve_uid(HolV2Machine *machine);
/* Positive node-visit budget for one atomic term operation; default 5000000.
    * Exhaustion is an execution/resource error, never logical failure. Nested
    * normalization/unification calls share a budget. Restore keeps the live
    * setting, so raising a limit is not undone by restoring a proof snapshot. */
int hol_v2_set_work_limit(HolV2Machine *machine, uint64_t visits);
uint64_t hol_v2_work_limit(const HolV2Machine *machine);

/* Unreachable terms, continuations and hypotheses are compacted between two
    * goals once the term heap has grown by its own size since the previous
    * collection, and by at least this many nodes (default 65536; 0 collects
    * before every goal). Identities exported to the host are kept. */
void hol_v2_set_collection_step(HolV2Machine *machine, size_t nodes);
size_t hol_v2_heap_count(const HolV2Machine *machine);
size_t hol_v2_collections(const HolV2Machine *machine);

/* Snapshots retain immutable program/index roots and copy mutable branch
    * state, including the proof-step boundary and service-view watermark.
    * The diagnostic legacy-copy switch copies the program too. Restoring
    * preserves the live monotonic UID/call/choice counters, so identities
    * created after a snapshot can never be reused. */
HolV2Machine *hol_v2_program_mark(HolV2Machine *machine);
int hol_v2_program_truncate(HolV2Machine *machine, const HolV2Machine *mark);
HolV2Machine *hol_v2_fork(const HolV2Machine *machine);
HolV2Machine *hol_v2_clone(const HolV2Machine *machine);
/* Like clone, but reports a typed, nonfatal allocation failure on machine. */
HolV2Machine *hol_v2_snapshot(HolV2Machine *machine);
int hol_v2_restore(HolV2Machine *machine, const HolV2Machine *snapshot);
/* Success transfers saved state and invalidates snapshot (destroy it normally).
    * Failure preserves both states. Retirement metadata may need headroom;
    * query arenas are never copied. The shared account/cap stays unchanged. */
int hol_v2_restore_consuming(HolV2Machine *machine, HolV2Machine *snapshot);

#endif
