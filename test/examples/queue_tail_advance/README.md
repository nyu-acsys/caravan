# Queue tail advancement

This example verifies `swing_tail`, a one-step Michael–Scott queue-tail
advancement operation. It is an additional verification example, with no matching
operation in Saturn's queue implementation.

The operation reads the queue's tail pointer and its cell, then attempts to move
the tail to the successor when one exists. Its contract requires `is_queue q`;
the queue invariant is preserved, and a caller's FIFO-view resource is framed.

`history_tail.ml` uses the history/sequence invariant and automatic access proofs.
`segment_tail.ml` uses the List/segment invariant and explicit access proofs.
Both include the empty-cell branch and the successful/failed CAS branches.

Dune appends each operation to its corresponding queue implementation and copies
that implementation's interface and companion proof into the build directory.
The generated files retain the original module names. The additional operation
has an inline checked contract and is not exported by either copied interface.
This shares the queue representations and proof definitions with the Saturn
case studies without maintaining another copy of them.

Run both proofs with:

```sh
dune build @test/examples/queue_tail_advance/runtest
```
