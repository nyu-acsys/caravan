# Stack drain client

Adapted from `Test.drain` in Saturn's
[stack tutorial](https://github.com/ocaml-multicore/saturn/blob/50d8d9d0a99b40434ab05bee49200cd5ffa028f5/doc/motivation.md).
The client retains the tutorial's polymorphic `Test (Stack : S)` functor and
the local `loop ()` helper capturing `st`. The annotated `S` signature lives in
`stack_intf.mli`. A small `Saturn_stack` adapter maps its `create`, `push`, and
`pop` operations to Treiber's interface, and a top-level `drain` wrapper preserves
the client API.

The contract in `stack_drain.mli` requires exclusive ownership of a stack with
contents `xs`. Draining returns `xs` in stack order and leaves the stack empty.
All implementation annotations are in `stack_drain.proof`, including the generic
loop contract and adapter proofs. The proof establishes partial correctness;
it does not prove termination. The tutorial's parallel spawning harness and its
barrier variant remain outside this example, so this is not whole-tutorial
source parity.

Dune copies the existing Treiber interface into this directory for interface-only
importing. The regression verifies the stack implementation against the original
interface, then verifies the adapters and client against the generated copy.
The client cannot use the stack's representation predicate definition.
The negative tests reject an always-empty
result and preservation of the original stack contents.

`raising_call.ml` calls the interface's `pop_exn`, handling its `Empty` in one client
and declaring it in the other's `raises` clause. The negative tests reject an undeclared
raise and a `raises` clause that the interface's contract does not imply.
