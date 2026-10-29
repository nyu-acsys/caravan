# Functor-wrapped Michael–Scott queues

Both the history-based and segment-based queue proofs are instantiated twice from
a unit functor. Each complete implementation and companion proof is verified once
in a shared Raven worker; the two applications have fresh layouts and resources.
An alias retains the identity of its original application.

Dune copies the original implementation, interface contracts, and proof bodies
verbatim from the two Saturn queue directories, adding only module headers,
applications, and clients. No queue-specific annotations or proof lemmas are added.
The canonical Saturn sources remain separate.

Clients cover empty, singleton, and longer `of_list` initializations, FIFO push/pop,
emptiness, and independent queues from both applications. Checks verify the complete
programs in process and as standalone emitted Raven, count shared worker/helper
bodies and fresh layouts, and reject hidden helpers, crossed application types, and
incorrect FIFO expectations. Negative checks fail through type checking or an
ordinary assertion failure rather than solver timeouts.

Run the examples with:

```sh
dune build @test/examples/functor_ms_queue/runtest
```

Use a Raven executable from the revision linked into Caravan for emitted proofs.
