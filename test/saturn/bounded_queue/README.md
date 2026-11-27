# Saturn bounded queue

This case study extracts the node, constructor, insertion, peeking, removal,
emptiness, snapshot, and access-helper layer of
Saturn's safe bounded queue at
[revision 50d8d9d](https://github.com/ocaml-multicore/saturn/tree/50d8d9d0a99b40434ab05bee49200cd5ffa028f5/src/bounded_queue).
The safe header supplies the node declarations, `make_node`, link conversion,
next-link reads, and next-link CAS. The body supplies capacity/counter accessors,
the queue declaration, `create`, `of_list_exn`, `capacity_of`, `fix_tail`, `push_as`, `try_push`,
`push_exn`, `peek_as`, `peek_opt`, `peek_exn`, `pop_as`, `pop_opt`, `pop_exn`, and
`drop_exn`, `is_empty`, `snapshot`, and `length`. The `is_full` query is corrected
to compare `length` with the capacity, using the snapshot helping protocol instead
of a potentially stale capacity cache. `of_list_exn` initializes cached capacity
from the remaining free slots. Insertion checks the sampled tail's next link before
reporting `Full`; a nonterminal node causes traversal and retry. The copyright and
license notice is retained from the body. A source-parity test pins this extraction
after removing Caravan field attributes, including these local queue fixes.

The `fenceless_get = Atomic.get` alias is eta-expanded for the translator. The
snapshot body retains the upstream helping and head-validation protocol.

The companion proof establishes a chain invariant with distinct node identities,
unbounded logical positions related to wrapping machine counters, publication
bounds, payload journals, and conservative capacity certificates. The `create`
contract requires a nonnegative capacity and supplies an empty abstract view.
Advancing the logical head preserves the chain resources and relaxes capacity
bounds, including for retained nodes behind the head. The invariant permits the
tail pointer to lag behind the head. `of_list_exn` preserves the input list in FIFO
order and rejects lists larger than the requested capacity. During private list
construction, each node's incoming view covers its suffix; final head publication
makes those views available. A next link's release lower bound is tracked separately
so that the same invariant also supports concurrent insertion.

`make_node` retains private payload/capacity journals and writable counter
ownership. Private capacity journals may contain several writes, as retries
reinitialize a candidate. The dummy counter is frozen before `create` publishes its head and
tail. The helper clients separately check candidate initialization, joint field
publication through a successful CAS, acquired counter reads, stale eligible
capacity reads, and counter rewriting after a definite failed CAS. Negative tests
reject early freezing, latest-value claims, forged visibility evidence, and null
conversion. Helper clients are regression programs, not upstream queue code.

Insertion has a logically atomic append contract. The proof covers positive
capacity refreshes, failed-CAS traversal and candidate reuse, successful link
publication, and tail helping. Explicit `opens` clauses describe access to the queue invariant and the
frozen-counter invariant family. Clients carry that counter footprint as well.
The structural chain lemmas use `opens {}` because they rearrange predicates
without opening invariants. `fix_tail` preserves the invariant without promising
that the tail equals its argument when it returns. Insertion has exact capacity
conditions: success requires space and failure requires fullness at its
linearization point. A Boolean prophecy predicts the final next-link check;
a failing attempt can linearize at the earlier head read, while a nonterminal
sampled tail causes retry. The proof covers machine-counter wraparound without a
bound on how long a producer may remain paused.

Peeking has an exact FIFO-head contract, including empty results and exceptions.
The proof retains a raw payload observation until the final head check, then
reconciles that event with the current journal and excludes cleared values only
on the validated branch. Clients check empty queues and both public peek wrappers
after insertion.

Removal linearizes at the successful head CAS. A fractional ghost cleanup flag
reserves the payload for the winner until its read and clear; earlier removers
may finish clearing after later head advances. The option, value, and discard
wrappers have FIFO contracts. Clients cover empty removals and a FIFO sequence
that peeks, discards, and reuses capacity after clearing.

Emptiness has an exact contract. Each reader registers its observation; enqueue
can complete a pending nonempty result when it links a node, allowing that reader
to finish after later removals. Registrations retain the sampled node and the
original reader token, and are retired after the next-link read.

Snapshot and length have exact logically atomic contracts. A one-shot Boolean
prophecy predicts the final head-validation outcome for each snapshot attempt.
The terminal next-link read commits only a successful attempt; a failed head
check resolves its prediction and retries with the atomic update still pending.
Frozen counter observations then recover the length across machine-counter
wraparound. Fullness delegates to the atomic length contract, including at zero
capacity. Client tests cover insertion, fullness, length, removal, and capacity
reuse. Client negatives reject an incorrect fullness result; the focused prophecy tests
check resolution obligations.

A deterministic native runtime fixture uses signed three-bit counter arithmetic
to exercise a stale producer across wraparound. Both public insertion wrappers
succeed with the repair and report a spurious `Full` when its next-link check is
removed. Genuine-full and zero-capacity cases remain covered. This reduced-width
fixture is separate from the full-width symbolic proof.

List construction has sequential native runtime coverage for FIFO order, empty and
spare-capacity queues, full capacity-one construction, oversize input, and zero
capacity. The reduced-width wraparound fixture is separate from the full-width
symbolic proof. The proof does not establish a refinement to OCaml's memory model.
