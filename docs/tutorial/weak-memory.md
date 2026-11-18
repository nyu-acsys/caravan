# 4. Weak memory

OCaml's ordinary mutable fields are not sequentially consistent atomics. Most
Caravan proofs can nevertheless use ordinary ownership and reason about their
values directly. More advanced algorithms deliberately allow some ordinary
accesses to race; these need an explicit field discipline and a proof of which
observations are safe.

This chapter develops a job descriptor in stages: first with exclusive ownership,
then with a frozen workload and a relaxed progress estimate. A separate result-slot
example introduces speculative payload validation. These examples use manual
proofs in companion `.proof` files; their runtime bodies contain no proof steps.

## Default fields and local race freedom {#sec:default-fields-and-local-race-freedom}

The default rules are the familiar ownership rules from
[contracts and ownership](./contracts#sec:function-contracts-and-heap-ownership):
a positive permission fraction allows a read, and full ownership allows a write.
Compatible read fractions agree on the value. A writer cannot coexist with another
reader or writer holding permission for the same location.

Here a job has an immutable identifier and a mutable amount of work. The preparing
domain changes the work, then hands the job to a worker:

<<< ../examples/owned_job.ml{caravan}

The contracts track ownership through preparation and inspection:

<<< ../examples/owned_job.proof{proof}

`Ghost.Task` associates the worker call with its contract. `Domain.spawn` transfers
its required resource to the worker; `Domain.join` returns the postcondition.
The parent cannot inspect or change `job.work` while the worker owns it. Readers
can instead share positive fractions when their contracts preserve those fractions.
No weak-memory annotations are needed for this default discipline.

OCaml's **data-race-freedom guarantee** allows sequentially consistent reasoning
for correctly synchronized programs. Its **local** guarantee extends sequential
reasoning to appropriately isolated, race-free portions of programs that may race
elsewhere. This is why an unrelated race need not invalidate a private computation.
See the [OCaml memory-model chapter](https://ocaml.org/manual/5.5/memorymodel.html)
for the guarantee and its boundaries.

Caravan's default contracts enforce exclusive writes and compatible reads; real
synchronization operations support ownership handoffs. This is not a rule that any
fraction of ownership acts as a fence. Isolation must hold over the relevant
execution, including transitions into and out of a protected region. An ordinary
load remains non-atomic: opening a shared invariant around it does not make it a
legal atomic access.

The advanced encodings below track visibility explicitly. Currently Caravan
rejects default mutable-field accesses in an execution using that encoding.
Keep default storage separate or choose an appropriate explicit discipline for
its fields. Immutable fields remain supported. The default and advanced jobs
are therefore separate versions of the example.

## Publication and acquired visibility {#sec:publication-and-acquired-visibility}

Two facts must be distinguished:

- **A fact about shared storage:** for example, a field has been frozen at `42`.
- **Visibility for an executing domain:** the domain has acquired the writes
  needed to read that field as `42`.

Sharing a persistent storage fact does not itself supply the second fact. An
actual runtime operation supplies synchronization: for example, an atomic
publication followed by an acquiring atomic access, spawning a worker, joining a
worker, or a mutex handoff. OCaml's `Atomic` operations remain sequentially
consistent: release/acquire here describes their effect on ordinary memory,
not a new choice of memory-order flags.

The proof records visibility using ghost write markers and sets of markers.
A marker identifies a checkpoint in the proof; creating or copying one does not
execute a runtime fence. `Ghost.self` denotes the current executor, and field
facades expose `visible` predicates indexed by that executor. The supported
handoff machinery propagates those facts at the corresponding runtime operation.

For explicit atomic publication, `Ghost.release_scope` supplies the published
view to the attached operation and `Ghost.acquire_scope` obtains a covered view
from the attached access. The field facade's `release`, `covered`, and
`observe`/`acquire` operations connect the view to the particular field discipline.
The view is a lower bound on acquired knowledge, not a complete description of
all memory visible to the runtime.

Our jobs use `Domain.spawn` so that the first examples can focus on the field
rules. The task mechanism transports the applicable visibility facts to the
worker. Reading an arbitrary atomic cell is not sufficient: the proof must link
the synchronization to the writes whose visibility is required.

## Immutable and frozen fields {#sec:immutable-and-frozen-fields}

An immutable record slot cannot change after initialization. Reading `job.id`
returns its initialized value, including when other locations have races.
However, an immutable slot containing a pointer does not make the pointed-to
object immutable, and reading the pointer does not acquire its later mutations.

A **frozen** field is mutable during preparation and becomes immutable through a
checked proof protocol. This supports descriptors whose final workload is known
only after construction:

<<< ../examples/frozen_job.ml{caravan}

The proof introduces a facade for the field, seals it on return from `create`,
and requests frozen reads for `workload`:

<<< ../examples/frozen_job.proof{proof}

`Ghost.Frozen` selects the declared field; it does not allocate another runtime
cell. Before freezing, full ownership permits writes and private reads use the
recorded writer's visibility. Transferring private storage to another writer
requires acquiring the preceding write's visibility; possession of the storage
resource alone is insufficient.

`Total.freeze job` consumes private ownership and establishes a persistent frozen
fact. Subsequent writes are forbidden by the proof protocol. It adds no runtime
instruction. `Total.visible Ghost.self job total` combines that frozen fact with
the current executor's acquired visibility of its final write.

`Ghost.frozen_scope` wraps the source load selected by `at (job.total)`. Calling
`read ()` performs that exact load; the wrapper does not insert an atomic load.
The frozen fact excludes later writes, and acquired visibility excludes older
values, so the result is exactly `total`.

The parent and worker can both retain the visibility fact. In `client`, they read
the same frozen workload and the equality assertion verifies. The immutable `id`
is protected by the small `identity` invariant: its read can use that invariant
because the slot has no subsequent writes. It acquires no visibility for `total`.

The same example includes explicit atomic publication. `publish` obtains a view
with `Total.release` and supplies it to `Atomic.make` through a release scope.
Its ghost return value names that view. The `Total.covered published job total`
postcondition connects the frozen field to it. In `receive`, the atomic load
acquires the covered view and `Total.observe` establishes the executor's
field-specific visibility before the frozen load.

## Relaxed fields and write journals {#sec:relaxed-fields-and-write-journals}

Now add a progress estimate that may change after publication:

<<< ../examples/relaxed_job.ml{caravan}

`total` remains frozen. `completed` uses `[@caravan.relaxed]`, allowing ordinary
reads and writes whose proof accounts for weak observations. This attribute does
not change OCaml's generated runtime operation or promise an atomic counter.
In particular, a read-modify-write expression on the field is not an atomic
increment.

The proof declares a second facade:

```proof
module Progress = Ghost.Relaxed (struct
  let field (job : job) = job.completed
end)
```

A relaxed field has a **write journal** containing pairs `(event, value)`. An
unrestricted read may select any entry in that journal. Its result need not be
the current value, and observing an entry does not acquire the write's visibility.
Even successive reads need not produce an increasing sequence.

`Progress.state job current writes` exposes the complete journal while hiding
publication metadata. `current` records the last executed write in the model; it is not a promise about
what the next reader will observe. `Progress.observe job value` returns an event
for the observation, and `Progress.observed job event value` records a persistent
fact about that journal entry. Such a fact remains useful after later writes.

An invariant can constrain every entry, allowing a read to establish the same
constraint despite staleness. For example, if every write is between `0` and a
fixed limit, every unrestricted read is within those bounds. The job example adds
a preparation value of `-1` to demonstrate when a stronger argument is necessary.

## Publication cuts and bounded observations {#sec:publication-cuts-and-bounded-observations}

`create` first initializes `completed` to `-1`, then writes `0` before publishing.
We want acquired readers to obtain a value between `0` and `total`, although the
complete write journal still contains `-1`.

The proof tracks two sets: `all`, the complete journal, and `eligible`, the entries
available to an acquired published read:

<<< ../examples/relaxed_job.proof{proof}

During preparation, writes form an ordered private chain. `Progress.publish job`
establishes a **publication cut** at its final write. Initially `eligible`
contains only that write of `0`; later writes extend both journals. Publication
is a ghost operation, so the cut still needs to reach readers through real
synchronization. `Progress.visible Ghost.self job` records the acquired cut.

`Progress.shared_state job current all eligible` exposes the published state.
The `progress` invariant bounds all entries below by `-1`, but bounds eligible
entries below by `0`. `set_completed` preserves both properties when it adds a
new value between `0` and the limit. It promises bounds, not that each new value
exceeds the preceding one.

`sample_unrestricted` reads from `all`, giving only the weaker lower bound.
`sample` requests `Ghost.published_scope` and requires acquired visibility; its
observation must belong to `eligible`, establishing the stronger lower bound.
Changing that wrapper to an ordinary scope makes the stronger proof fail.
Acquiring the cut excludes preparation values; it does not promise freshness
with respect to subsequent writes.

In `client`, spawning `finish` transfers the frozen workload's visibility to the
worker. The parent samples progress while the worker may update it. The estimate
is bounded, but the proof does not claim that it equals `total`, even after the
join: the local estimate was obtained before the join.

The explicit `[limit : int]` arguments are ghost parameters: access wrappers pass
the bound to helper contracts without changing runtime calls. The `opens` clauses
on `finish` and `client` allow their callees to open the frozen-field and progress
invariants. They describe the proof's invariant mask, not memory fences.

The publication protocol requires an ordered private prefix. An unordered write
by another executor invalidates that private-chain certificate; simply recording
the most recent writer cannot repair it. After publication, relaxed writes remain
allowed and need only preserve the journal invariant.

## Raw result slots and validation {#sec:raw-result-slots-and-validation}

Some algorithms clear a payload slot after retiring its object, to release a
reference for garbage collection. A reader may load the payload before checking
whether the object is still live. This needs a representation argument in
addition to relaxed-memory reasoning.

The following small example uses a monotone retirement flag. Once `head` is true,
the slot is retired and its payload may be cleared:

<<< ../examples/raw_result.ml{caravan}

`[@caravan.raw]` is an additional discipline on a relaxed field. The supported
`Obj.magic ()` occurrence is a specific clearing marker; this does not enable
general unsafe casts. Raw journals use a logical option carrier: `Some value`
for an admissible payload write and `None` for a cleared word. Those options are
proof representations, not the runtime storage layout.

A raw load produces a speculative value. `Ghost.raw value` describes its journal
representation without claiming that it is a valid ordinary payload. Before
validation, the value cannot be returned as a payload, passed to ordinary
consumers, dereferenced, or pattern-matched as its source type.

The proof records retirement before clearing and reconciles the selected journal
entry at the following atomic validation:

<<< ../examples/raw_result.proof{proof}

`peek` loads the payload first, then reads the flag. A cleared observation implies
that retirement has already occurred. Because the flag never returns to false,
a validation observing false rules out a cleared entry. The proof then establishes
`Ghost.raw value === Some initial`, making it legal to return `Some value` on that
branch. The retired branch discards the speculative value and returns `None`.
Returning `Some value` on both branches is rejected.

The validation argument depends on this lifetime protocol and the source ordering
between the load and its atomic check. An arbitrary later atomic access does not
validate a payload. Algorithms that reuse states also need an appropriate no-ABA
argument. See the [OCaml runtime's memory-model note
MM](https://github.com/ocaml/ocaml/blob/5.5/runtime/memory.c) for the ordering boundary
underlying this pattern.

## Choosing a discipline {#sec:choosing-a-discipline}

| Need | Discipline |
| --- | --- |
| Private mutation or synchronized ownership transfer | Default ownership |
| A value fixed at allocation | Immutable field |
| Private preparation followed by shared exact reads | Frozen field plus acquired visibility |
| Stale observations constrained by a write invariant | Relaxed field and complete journal |
| Exclude preparation writes after acquiring publication | Relaxed field with a publication cut |
| Speculative loads of storage that may contain a clearing word | Raw relaxed field plus validation |

These are proof disciplines for existing source operations. Annotations do not
insert fences, turn ordinary increments into atomic ones, or establish
linearizability by themselves. The journal invariants, actual synchronization,
and operation contracts still have to justify the desired behaviour.

The source listings above link to the examples and their companion proofs.
Save each `.ml` beside its matching `.proof` and run:

```bash
caravan owned_job.ml
caravan frozen_job.ml
caravan relaxed_job.ml
caravan raw_result.ml
```

The [Saturn bounded queue](https://github.com/nyu-acsys/caravan/tree/main/test/saturn/bounded_queue)
uses these disciplines together in a larger data-structure proof.

Continue with [OCaml coverage](./ocaml-subset) and
[semantics and verification limits](./semantics).
