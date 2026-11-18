# 4. Weak memory

OCaml's ordinary mutable fields are not sequentially consistent atomics: when two
domains access the same field without synchronization, a read may return an older
value than the most recent write. Most Caravan proofs never encounter this, because
ownership already rules out such races, and the proof can reason about field values
as in a sequential program. Some concurrent algorithms, however, deliberately let
ordinary fields race. Verifying them requires stating, for each such field, which
values a racing read may return.

Caravan does this through **field disciplines**: per-field rules that determine what
a proof must establish before a read or write, and what it learns from a read. This
chapter introduces them one at a time:

| Discipline | Annotation | A read returns |
| --- | --- | --- |
| Default | none | the current value, given ownership |
| Immutable | none (an immutable field) | the initialized value |
| Frozen | `[@caravan.frozen]` | the final value, once the field is frozen and its last write is visible |
| Relaxed | `[@caravan.relaxed]` | some earlier write, constrained by a proof invariant |
| Raw | `[@caravan.relaxed] [@caravan.raw]` | a speculative value that must be validated before use |

## The running example {#sec:weak-memory-example}

The chapter follows a **job descriptor**: a small record that one domain prepares and
then hands to a worker domain. It describes a unit of work by an identifier `id` and
the amount of work to be done. A later version adds `completed`, an estimate of the
progress the worker has made. The versions are:

- [`owned_job.ml`](../examples/owned_job.ml): the preparing domain sets the amount
  of work and then passes the whole job to the worker. Only one domain accesses the
  job at a time, so default ownership suffices.
- [`frozen_job.ml`](../examples/frozen_job.ml): the amount of work, now `total`, is
  written during creation and never changes afterwards. Both domains read it
  concurrently without owning it. The example also passes the job through an
  atomic channel.
- [`relaxed_job.ml`](../examples/relaxed_job.ml): the worker records its progress in
  `completed` while the preparing domain reads it concurrently, racing with those
  writes. The proof bounds the values such a read can return.

A separate example, [`raw_result.ml`](../examples/raw_result.ml), shows a result slot
that is cleared after use, and a reader that loads the slot first and only afterwards
checks whether the load was still valid.

All examples use manual proofs in companion `.proof` files; the OCaml code contains
no proof steps. Each version is a separate program because of a current restriction:
once a program uses frozen or relaxed fields, Caravan rejects reads and writes of
default mutable fields anywhere in that program. Immutable fields remain supported
alongside them.

## Default fields and local race freedom {#sec:default-fields-and-local-race-freedom}

Unless a mutable field is annotated otherwise, Caravan verifies its reads and writes
with the ownership rules from
[contracts and ownership](./contracts#sec:function-contracts-and-heap-ownership):
reading a field requires a positive fraction of its ownership, and writing it
requires full ownership. Domains that hold fractions of the same field agree on its
value, and while one domain can write a field, no other domain can read or write it.

In the first version of the job, `id` is immutable and `work` is mutable. The
preparing domain sets `work` and then hands the job to a worker:

<<< ../examples/owned_job.ml{caravan}

The contracts state which ownership each function needs and returns:

<<< ../examples/owned_job.proof{proof}

`Ghost.Task` attaches a contract to the function that the worker runs, here
`inspect`. `Domain.spawn` transfers the resources that this contract requires to
the worker, and `Domain.join` returns what it ensures. Until the join, the parent
no longer owns `job.work`, so it can neither read nor change it. If several
domains only need to read a field, they can instead share fractions of its
ownership. None of this needs any weak-memory annotation.

Why is ownership enough here? OCaml guarantees that a program without data races
behaves as if its accesses were sequentially consistent. Its **local** version of
this guarantee also covers parts of a program that are race-free even when other
parts race, so a race on one location does not affect reasoning about a private
computation elsewhere. Ownership rules out races on the fields it covers, which is
what lets Caravan reason about their values as in a sequential program. The
[OCaml memory-model chapter](https://ocaml.org/manual/5.5/memorymodel.html)
describes the guarantee and its limits.

Ownership itself is not synchronization. Moving ownership of a field from one domain
to another is only sound at an operation that really synchronizes the two domains,
such as `Domain.spawn`, `Domain.join` or a mutex; the contracts of those operations
are what transfer ownership. Holding a fraction of ownership does not act as a
fence, and race freedom must hold over the whole execution, including the
transitions into and out of the code that relies on it. Likewise, reading or writing
a default field is not an atomic step, so a proof cannot open a shared invariant
around it the way it can around an `Atomic` operation. Caravan rejects such an
access with the error "Cannot take a non-atomic step while an invariant or atomic
update is open."

## Publication and acquired visibility {#sec:publication-and-acquired-visibility}

The remaining disciplines allow a domain to read a field that it does not own. The
proof then has to show that the reading domain has seen the write it relies on, and
it must keep apart two kinds of facts:

- **A fact about the shared field,** for example that a field has been frozen with
  the value `42`.
- **A fact about what an executing domain has seen,** for example that the domain
  has synchronized with the write of `42`, so that reading the field returns `42`.

A fact of the first kind can be shared freely, but sharing it does not provide the
second. Only a runtime operation that synchronizes domains provides the second kind:
an atomic write followed by an atomic read of the same location, spawning or joining
a worker, or handing over a mutex. In the terms used below, the atomic write
**releases** the writer's earlier writes and the atomic read **acquires** them.
OCaml's `Atomic` operations are always sequentially consistent; release and
acquire describe what they make visible about ordinary fields, not separate memory
orders that a program can choose.

Proofs track what a domain has seen with ghost values:

- A **write marker** (of type `Ghost.t`) names a point in a domain's sequence of
  writes. Creating or copying a marker has no runtime effect.
- A **view** is a set of markers. It is a lower bound on what a domain has seen,
  not a complete description of the memory visible to it.
- `Ghost.self` denotes the domain executing the current code.
- Each frozen or relaxed field gets a **facade**, a ghost module that provides the
  field's predicates and operations. Its `visible` predicate, indexed by a domain
  such as `Ghost.self`, states what that domain has seen of the field.

The contracts of `Domain.spawn`, `Domain.join` and the mutex operations transfer
these facts automatically. For an explicit atomic handoff, the proof wraps the
atomic operations: `Ghost.release_scope` attaches a view to an atomic write, and
`Ghost.acquire_scope` obtains that view from an atomic read of the same location.
The facade's `release`, `covered` and `observe` operations connect such a view to
the field.

The jobs below mostly use `Domain.spawn`, so that the examples can concentrate on
the field rules. Note that reading some unrelated atomic does not help: the proof
must connect the synchronizing operation to the particular writes that need to be
visible.

## Immutable and frozen fields {#sec:immutable-and-frozen-fields}

An immutable field cannot change after the record is initialized, so a read
returns its initial value, regardless of races on other fields. If the field holds
a pointer, though, the object it points to is not thereby immutable, and reading
the pointer does not acquire that object's later changes.

A **frozen** field may be written while its record is being prepared and becomes
immutable once the proof freezes it. This suits fields whose final value is only
known after allocation, such as the job's `total`:

<<< ../examples/frozen_job.ml{caravan}

The proof creates a facade `Total` for the field, freezes the field when `create`
returns, and reads it in `workload` through a frozen read:

<<< ../examples/frozen_job.proof{proof}

`Ghost.Frozen` creates the facade for the field that `field` selects; it does not
allocate a runtime cell. Before the field is frozen, writing it requires full
ownership, and the owning domain can read it because it has seen its own writes.
To pass the unfrozen field to another writer, that writer must first acquire the
previous write; transferring ownership alone is not enough.

`Total.freeze job` gives up ownership of the field and establishes a persistent
fact that the field is frozen; the proof rejects any later write. Freezing executes
no runtime instruction. `Total.visible Ghost.self job total` combines the frozen
fact with the fact that the current domain has seen the final write, of `total`.

In `workload`, `Ghost.frozen_scope` wraps the load selected by `at (job.total)`.
Calling `read ()` performs exactly that load; the wrapper does not make it atomic.
Because the field is frozen, no newer value can exist, and because the domain has
seen the final write, no older value can be returned, so the read yields exactly
`total`.

Spawning the worker in `client` passes this visibility fact on, so the parent and
the worker read the same `total` and the final assertion verifies. Reading the
immutable `id` in `identifier` relies on the small `identity` invariant, which holds
ownership of `id`; this is possible because `id` is never written again. Reading
`id` acquires nothing about `total`.

The same example also passes the job through an atomic channel. In `publish`,
`Total.release` obtains a view that includes the final write of `total`, and the
release scope attaches it to the channel created by `Atomic.make`. The ghost return
value `published` names this view, and `Total.covered published job total` states
that it includes the final write. In `receive`, the atomic read acquires the view,
and `Total.observe` turns it into the domain's visibility of `total`, which the
frozen read then needs.

## Relaxed fields and write journals {#sec:relaxed-fields-and-write-journals}

The third version adds a progress estimate, which the worker updates after the job
has been shared:

<<< ../examples/relaxed_job.ml{caravan}

`total` is still frozen. `completed` is annotated `[@caravan.relaxed]`: other domains
may read and write it concurrently with ordinary loads and stores, and the proof must
account for reads that return outdated values. The annotation does not change the
code OCaml generates, and it does not make the field an atomic counter; in
particular, an expression that reads and then writes the field is not an atomic
increment.

The proof declares a second facade for it:

```proof
module Progress = Ghost.Relaxed (struct
  let field (job : job) = job.completed
end)
```

Caravan models a relaxed field by its **write journal**: the set of all writes to
the field, each a pair `(event, value)` of a write marker and the written value. An
unrestricted read may return the value of any write in the journal. It need not be
the latest one, observing a write does not acquire that write's visibility, and two
successive reads may even return values in decreasing order of their writes.

This model over-approximates OCaml's actual weak-memory behavior. Every value that
OCaml's memory model allows a racing read to return comes from a write in the
journal, but the journal also contains writes that OCaml rules out, such as writes
older than one the reading domain has already made or acquired. A proof about a
relaxed field is therefore sound, but some properties that hold for the running
program cannot be proved with this model alone.

`Progress.state job current writes` describes the full journal, where `current` is
the value of the most recent write. That is a fact about the order of writes, not a
promise about what the next read returns. `Progress.observe job value` returns the
marker of the write that a read observed, and `Progress.observed job event value`
records that observation as a persistent fact, which remains true after later
writes.

Because a read can return any write in the journal, an invariant that constrains
every write also constrains every read. For example, if every write of `completed`
lies between `0` and the job's total, so does every read, however outdated. The job
writes `-1` while it is being prepared, which breaks this simple argument; the next
section shows how to rule that value out.

## Publication cuts and bounded observations {#sec:publication-cuts-and-bounded-observations}

`create` first initializes `completed` to `-1` and then sets it to `0` before the job
is shared. A domain that has acquired the job should read a value between `0` and
`total`, even though the journal still contains the write of `-1`.

The proof therefore tracks two sets of writes: `all`, the full journal, and
`eligible`, the writes that a domain that has acquired the publication can still
observe:

<<< ../examples/relaxed_job.proof{proof}

While the job is private, its writes to `completed` happen in one domain, in a known
order. `Progress.publish job` places a **publication cut** after the last of them.
Initially, `eligible` contains only that last write, of `0`; later writes are added
to both sets. Publishing is a ghost operation, so the cut still has to reach other
domains through a real synchronizing operation, here `Domain.spawn`.
`Progress.visible Ghost.self job` states that the current domain has acquired the
cut.

`Progress.shared_state job current all eligible` describes the field after
publication. The `progress` invariant bounds every write in `all` by `-1` from below
and every write in `eligible` by `0`, and both by `limit` from above.
`set_completed` preserves the invariant for any new value between `0` and `limit`.
It guarantees these bounds, not that each new value is larger than the previous one.

`sample_unrestricted` reads without having acquired the cut, so its result is only
known to be in `all`, which gives the weaker lower bound `-1`. `sample` uses
`Ghost.published_scope` and requires the domain to have acquired the cut, so its
result is in `eligible`, which gives the lower bound `0`. Replacing that wrapper by
an ordinary scope makes the proof of the stronger bound fail. Acquiring the cut
excludes the values written during preparation, but it does not make the read
return the latest write.

In `client`, spawning `finish` passes the visibility of the frozen `total` to the
worker, which then sets the progress to `total`. Meanwhile, the parent samples the
progress. The proof shows that the sample lies between `0` and `total`, but not that
it equals `total`: the parent took the sample before joining the worker.

The bracketed `[limit : int]` parameters are ghost parameters, which pass the bound
to the contracts of helper functions without changing the runtime calls. The `opens`
clauses of `finish` and `client` allow their callees to open the invariants of the
frozen field and of the progress. They concern the proof's invariant masks and have
nothing to do with memory fences.

The publication cut relies on the private writes having happened in one known order.
A write by another domain before publication breaks this, and remembering which
domain wrote last does not repair it. After publication, relaxed writes are
unrestricted except that they must preserve the journal invariant.

## Raw result slots and validation {#sec:raw-result-slots-and-validation}

Some concurrent data structures clear a slot once the object it belongs to is
retired, so that the garbage collector can reclaim the slot's contents. A reader may
then load the slot before it checks whether the object is still live, and the value
it loaded may be the clearing value rather than a real payload. Verifying such a
reader requires reasoning about what the loaded word represents, in addition to the
relaxed-memory reasoning above.

In the following example, an atomic flag `head` marks the slot as retired. The flag
only ever changes from `false` to `true`, and once it is `true`, the slot's payload
may be cleared:

<<< ../examples/raw_result.ml{caravan}

`[@caravan.raw]` adds rules on top of a relaxed field. Clearing the slot is written
`Obj.magic ()`; Caravan supports this one occurrence as the clearing value, not
unsafe casts in general. In the proof, the journal of a raw field holds options:
`Some value` for a write of a payload and `None` for a write that clears the slot.
These options are only how the proof represents the writes; the slot itself still
holds the payload or the clearing word.

A read of a raw field produces a speculative value. `Ghost.raw value` describes which
journal entry it represents, without claiming that it is a valid payload. Until the
proof has validated the value, the program may not return it as a payload, pass it
to other code, dereference it, or pattern-match on it as a value of the field's
type.

The proof records the retirement before the slot is cleared, and connects the entry
that the read observed to the atomic check of the flag that follows it:

<<< ../examples/raw_result.proof{proof}

`peek` loads the payload first and then reads the flag. If the load observed the
clearing write, the retirement had already happened, so the flag was already `true`.
Since the flag never becomes `false` again, a check that finds it `false` rules out
the clearing write. The proof then establishes `Ghost.raw value === Some initial`,
which makes returning `Some value` on that branch legal. On the other branch, the
speculative value is discarded and `peek` returns `None`. Returning `Some value` on
both branches is rejected.

This argument depends on the retirement protocol and on the program order between
the load and the atomic check that follows it. An atomic access somewhere else does
not validate the payload. Algorithms that reuse slots or states also need an argument
that rules out ABA problems. The
[memory-model notes in OCaml's runtime](https://github.com/ocaml/ocaml/blob/5.5/runtime/memory.c)
describe the ordering guarantee that this pattern relies on.

## Choosing a discipline {#sec:choosing-a-discipline}

| Need | Discipline |
| --- | --- |
| Private mutation, or ownership transfer at a synchronization point | Default ownership |
| A value fixed when the record is created | Immutable field |
| Private preparation followed by exact reads in several domains | Frozen field plus acquired visibility |
| Possibly outdated reads, constrained by an invariant on all writes | Relaxed field and its write journal |
| Excluding writes made before publication, for domains that acquired it | Relaxed field with a publication cut |
| Speculative loads of a slot that may hold a clearing value | Raw relaxed field plus validation |

These disciplines are proof rules for the existing source operations. The
annotations do not insert fences, make increments atomic, or establish
linearizability. Those properties still have to follow from the journal invariants,
the actual synchronization, and the operations' contracts.

The source listings above link to the examples and their companion proofs. Save each
`.ml` file beside its `.proof` file and run:

```bash
caravan owned_job.ml
caravan frozen_job.ml
caravan relaxed_job.ml
caravan raw_result.ml
```

The [Saturn bounded queue](https://github.com/nyu-acsys/caravan/tree/main/test/saturn/bounded_queue)
combines these disciplines in a larger data-structure proof.

Continue with [OCaml coverage](./ocaml-subset) and
[semantics and verification limits](./semantics).
