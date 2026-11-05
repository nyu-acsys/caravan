# Stack drain client

Adapted from `Test.drain` in Saturn's
[stack tutorial](https://github.com/ocaml-multicore/saturn/blob/50d8d9d0a99b40434ab05bee49200cd5ffa028f5/doc/motivation.md).
The client is polymorphic, lifted out of the tutorial's functor,
and calls `Treiber_stack.pop_opt` in place of `Stack.pop`. The recursive helper
is the exported `drain` function. The algorithm is unchanged.

The contract in `stack_drain.mli` requires exclusive ownership of a stack with
contents `xs`. Draining returns `xs` in stack order and leaves the stack empty.
The implementation needs no inline proof annotations or companion proof file.
The proof establishes partial correctness; it does not prove termination or a
parallel spawning harness.

Dune copies the existing Treiber interface into this directory for interface-only
importing. The regression verifies the stack implementation against the original
interface, then verifies this client against the generated copy. There is no
separately maintained library specification, and the client cannot use the stack's
representation predicate definition. The negative tests reject an always-empty
result and preservation of the original stack contents.

`raising_call.ml` calls the interface's `pop_exn`, handling its `Empty` in one client
and declaring it in the other's `raises` clause. The negative tests reject an undeclared
raise and a `raises` clause that the interface's contract does not imply.
