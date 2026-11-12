# Execution context and synchronization

The handwritten models check resource transfer and protocol consistency. They do
not yet implement Caravan's source-to-model translation or prove its refinement.

## One view per executing domain

`ThreadContext` owns one authoritative set of immutable publication cuts for each
logical executing identity. Every field-value family uses that same context.
`thread_clients.rav` checks that acquiring a Boolean publication imports an
integer field's cut. Persistent snapshots retain their owner index; copying them
through an invariant does not advance another domain's context.

A proposed simulation relation maps each cut to a partial concrete frontier. The
actual executing domain's frontier must dominate every cut in its abstract view.
The view may omit additional concrete knowledge. Cuts identify allocations and
writes, rather than just equal values.

## Publication and atomic operations

Freezing and publication have distinct semantic roles. Freezing seals the final
private write, which the writer already knows. Communicating it to another
domain requires an actual atomic publication and a matching synchronization
path. Folding an invariant alone is not that publication.

`ThreadedField.publish` combines sealing the private field with creating a fresh,
one-shot publication channel. Its `acquire` reads that specific channel. This
restricted model does not permit treating an arbitrary atomic load as acquisition
of a chosen field. A translator must justify the correspondence between the
source atomic location, its observed value, and that publication.

`ViewAtomic` adds a mutable atomic-reference model. Its slot points to an immutable
publication version; overwriting first imports the previous version's view, then
publishes the writer's combined view. The lower-bound contract survives every
overwrite. `overwrite_preserves_publication` checks that a third domain acquires
the original field's cut even after another domain overwrites the atomic payload.
The mutation test rejects dropping the previous release view. A fresh version is
model metadata, not a runtime allocation required of each source atomic write.

This follows the [OCaml 5.5 operational memory model](https://ocaml.org/manual/5.5/memorymodel.html):
atomic reads merge the location's frontier into the domain's frontier; atomic
writes merge both frontiers and update both. Thus location metadata accumulates
across overwrites. The prototype covers loads and stores. Successful and failed
CAS, exchanges, and other read-modify-write operations still need corresponding
rules before those source operations can use this translation mode.

## Spawn, completion, and join

`ViewForkJoin` uses Raven's actual `spawn`. The parent creates a fresh child
identity with its initial view, then transfers the child's authority to the
worker. The generic task receives that identity and returns its final context.
A completion invariant stores the result and final child authority. A linear
ticket allows the joiner to retrieve them once, after observing completion, and
to merge the child view into the parent. The checks reject a second join and a
parent read using visibility it has not yet acquired by joining.

The completion handoff is modeled as a physically atomic block. This checks the
ownership protocol; it is not a verification of OCaml's runtime implementation.
The [Domain API](https://ocaml.org/manual/5.5/api/Domain.html) waits for completion
and re-raises a child's uncaught exception. Both normal and exceptional completed
outcomes must therefore return the final context in Caravan's trusted facade.
The generic model can package either outcome in its task result, but the current
concrete client exercises normal completion only. Termination is not proved.

## Translator integration requirements

Extend the existing trusted `Domain_contract` resource-transfer mechanism rather
than introducing another task runtime. Thread the hidden executing identity and
entry view through the callback, and return final authority with every completed
outcome. Preserve the executing identity across ordinary procedure calls.

The model's `create_thread`, `fork_context`, and `join_context` are experiment
helpers. They cannot become arbitrary user-callable ghost transitions: creating
or choosing another identity must not let a source domain impersonate it. Joining
must be tied to the actual handle and completion, rather than merely obtaining a
foreign context from a shared invariant.

Before implementation, also connect cut creation to all protected source writes,
allocation identity, and every synchronization path. The
[runtime memory-model explanation](https://github.com/ocaml/ocaml/blob/5.5/runtime/memory.c#L40-L117)
supports keeping speculative reads followed by atomic validation separate from
frozen exact reads. Neither a raw history observation nor an arbitrary pure
validation condition supplies publication visibility.
