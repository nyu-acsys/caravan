# Shared ordinary-field protocol experiment

These handwritten Raven proofs explore two abstractions for word-sized OCaml
fields. They are verification models, not supported Caravan annotations or a
verification of Saturn's bounded queue.

Run the focused checks with:

```sh
dune runtest -j2 --force test/examples/shared_ordinary_fields
```

## Past writes and speculative validation

`past_writes.rav` provides a generic, append-only write journal backed by
`Auth[SetRA]`. Its abstract read chooses any recorded write. This deliberately
allows stale observations and does not impose read/read coherence. The single
`assume` in `sample` defines this nondeterministic choice; resource lemmas and
client proofs introduce no additional assumptions.

An observation is a persistent fragment of the journal. It certifies a past write
for that journal, but does not transfer ownership of the stored payload.

`payload.rav` instantiates this model for one publication/retirement epoch:

- The initial write contains a payload.
- A retirement event records advancement away from the old head.
- Clearing requires retirement evidence and records a discarded value.
- An observed clear therefore implies retirement already occurred.
- If the old head cannot return, an atomic validation that still observes it
  excludes a clear origin and establishes the initialized payload.

The raw result has explicit `payload` and `discarded` alternatives. These are
proof-model alternatives, not additional runtime tags or an implementation of
`Obj.magic`. A source translation would need to preserve unvalidated values
without asserting source-type admissibility or permitting unsafe operations on
them. The experiment only establishes payload validity after validation.

The head is abstracted to whether it has moved from one particular identity.
The actual queue proof must establish the retirement and absence-of-ABA facts
using its concrete representation. This model does not prove those facts for it.
Retirement evidence also grants no exclusive dequeuer right; proving the pop
operation requires a separate linear capability.

## Why the initial publication capability was insufficient

`publication.rav` is retained as the initial experiment. Its sealed `acquired`
predicate blocks direct reads without a capability, but that capability is an
ordinary transferable SL resource. `unindexed_transfer.rav` demonstrates the
problem: copying it from an invariant around an unrelated atomic read permits a
frozen read. Raven correctly verifies that SC model; interpreting it as
source-thread visibility would be unjustified.

The first cram test retains its local positive/negative checks. Their success
does not establish a cross-thread visibility discipline. `thread_views.t` adds
the transfer experiment and the replacement below.

## Thread-indexed views

`thread_views.rav` defines one shared `ThreadContext`, independent of field-value
types. It separates two resources:

```text
context(thread, view)  = authoritative ownership of that thread's view
seen(thread, lower)    = persistent lower-bound evidence about that same thread
```

Both use an authoritative set RA. `context` contains the exclusive authority;
`seen` contains an idempotent fragment. Seen evidence can be freely copied and
stored in shared invariants. Doing so preserves its thread index: a recipient
cannot turn `seen(writer, cut)` into `seen(recipient, cut)`, or use it to grow the
recipient's authoritative context.

Frozen reads require the context of the executing thread and membership of the
publication cut in that view. Publication metadata is represented as invariant outputs:

```raven
inv published(channel: Ref; cell: Ref, value: E, release: Set[Ref])
```

This binds the cell, value and release view by agreement to one channel; they
are not freely selectable invariant input identities. The mailbox invariants
likewise bind their sender and publication identity as output metadata.

A publication records the publisher's prior view;
a matching acquire joins that release view and the publication's cut into the
recipient's view. This also supports transitive synchronization through another
channel. An independently published channel carries no such release cut.

The publisher retains knowledge of its final private write. Synchronized fork
creates a fresh child identity with the parent's view; join consumes the returned
child context and merges its view into the parent's. Snapshots are duplicable,
but neither authority nor a joined child's context can be duplicated or reused.
There is no public operation that advances a view arbitrarily.

`thread_clients.rav` checks publisher reads, matching and transitive acquisition,
fork and join. `thread_mailbox.rav` permits an already-visible reader to use a
shared invariant and unrelated atomic read. The paired negative tests reject:

- obtaining recipient visibility from the invariant's writer snapshot;
- acquiring an independent channel instead of the publication channel;
- retargeting a persistent snapshot or using foreign context authority;
- duplicating an exclusive context;
- inventing a stronger release view;
- reusing a child context after join;
- calling the hidden arbitrary-advance helper.

The execution identity is explicit in this handwritten model. Raven does not
supply an implicit current-thread identity. A source translation must bind that
parameter to the actual executing domain and keep it fixed across ordinary
calls. Passing a writer identity in the model describes a writer operation; it
is not permission for a source reader to impersonate that writer. `thread_spawn.rav` additionally checks an actual Raven spawn and a linear
completion/join protocol; it does not run an OCaml program.

The handwritten clients also use explicit ghost views/values and invariant
namespace annotations. They measure the logical mechanism, not the eventual
annotation burden or inferred execution-context interface.

## Semantic boundary

The [OCaml operational memory model](https://ocaml.org/manual/5.5/memorymodel.html)
uses timestamped write histories and per-domain frontiers. Projecting each
location's history to its set of recorded write events, and dropping the frontier
restriction on reads, gives the intended simulation argument for `PastWrites`:
every concrete read selects a write the abstract model permits. Events are added
at their source writes; journal insertion order is not claimed to be the
coherence order of OCaml timestamps.

The [runtime's memory-model explanation](https://github.com/ocaml/ocaml/blob/5.5/runtime/memory.c#L40-L117)
explicitly describes the ordering needed for the clear/read/atomic-validation
pattern. For frozen fields, acquiring publication must establish a lower bound
at the last private write, and subsequent writes must remain forbidden. The
thread-indexed prototype represents these lower bounds as sets of immutable
publication cuts, rather than a full timestamp/frontier implementation.

Raven checks the protocols within these models. It does not establish the
source-to-model refinement. Before integration, that argument needs to cover
aliasing, every write and initialization, synchronization paths, raw values and
the interaction with existing race-free accesses. The thread-context binding,
release-view propagation and synchronized fork/join rules also need source
justification. A field cannot simultaneously
use incompatible history and current-value ownership interpretations.

## Additional experiments

- `thread_atomics.rav` checks that overwriting a mutable atomic reference retains
  earlier publication cuts.
- `thread_spawn.rav` checks a generic task's context transfer through actual
  Raven spawn, completion, and one-time join.
- `cached_counter.rav` checks conservative capacity-cache arithmetic under stale
  observations, with publication filtering tied to the executing context.

[Synchronization requirements](SYNCHRONIZATION.md) records the proposed source
correspondence and remaining integration obligations.
[Cache protocol](CACHE-PROTOCOL.md) explains the bounded queue pattern and the
limits of the mathematical-integer experiment. Full queue verification,
annotation design, machine-integer bounds, and concrete `Obj.magic` handling
remain outside these handwritten models.

## Raven invariant-presence regression

The stronger negative tests exposed a backend issue with presence tracking for
invariants without output parameters. Raven now uses a dedicated unit-agreement
algebra distinguishing absence, presence, and invalid composition, and retains
presence checks through heap transfers. The experiments were rechecked against
that repair. Invariant output metadata remains necessary to bind publication
values and release views by agreement; it is not a workaround for missing
presence checks.

[Field façade syntax](SYNTAX.md) describes the checked declaration front end and
the operational annotations still awaiting translator integration.
