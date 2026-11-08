# Stack drain client

Adapted from the barrier-free `Test` functor in Saturn's
[stack tutorial](https://github.com/ocaml-multicore/saturn/blob/50d8d9d0a99b40434ab05bee49200cd5ffa028f5/doc/motivation.md).
The client retains the tutorial's `Test (Stack : S)` functor, ten-push worker,
two-domain spawn/join harness, and polymorphic drain with its captured local
`loop ()`. The worker identifiers are integers `1` and `2`, and the worker loop
names its otherwise unused counter `i` for the proof. These are the only changes
to the tutorial functor's implementation bytes; a source-parity regression guards
the body after normalizing those two adaptations. The barrier variant remains
deferred.

The annotated `S` signature lives in `stack_intf.mli`. A small `Saturn_stack`
adapter maps its `create`, `push`, and `pop` operations to Treiber's interface.
Top-level `drain` and `test` wrappers expose the clients.

The contract in `stack_drain.mli` requires exclusive ownership for `drain`, which
returns the original contents in stack order and leaves the stack empty. The
parallel `test` returns twenty elements and their length. Its shared invariant
tracks both workers' contributions; joining their task handles recovers the
resources needed to take the stack back out of the invariant before draining.
Result order may vary with scheduling.

All implementation annotations are in `stack_drain.proof`, including the worker
loop invariant, generic drain loop contract, task facade, and adapter proofs.
Verification establishes partial correctness; it does not prove termination.

Dune copies the existing Treiber interface into this directory for interface-only
importing. The regression verifies the stack implementation against the original
interface, then verifies the adapters and client against the generated copy.
The client cannot use the stack's representation predicate definition.
The negative tests reject an always-empty result, preservation of the original
stack contents, a worker that returns after nine pushes, and a missing join.

`raising_call.ml` calls the interface's `pop_exn`, handling its `Empty` in one client
and declaring it in the other's `raises` clause. The negative tests reject an undeclared
raise and a `raises` clause that the interface's contract does not imply.
