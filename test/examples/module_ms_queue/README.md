# Module-wrapped history queue

This integration example places the complete history-based Michael–Scott queue
behind a static `Queue` module signature. `Alias` names the same module, and
clients check creation, list initialization, FIFO push/pop, and emptiness through
that alias.

Dune wraps the implementation, interface contracts, and companion proof directly
from `test/saturn/michael_scott_queue`. The implementation and proof bodies need
no additional annotations. The generated `module_queue.ml` and
`module_queue.proof` exercise scoped state records, views, actions, histories,
helping, recursive builder predicates, and auxiliary lemmas together. The canonical
Saturn sources remain separate.

The checks verify the complete program in process and as emitted Raven. A client
checked against the same generated interface is rejected when it expects the wrong
FIFO value. Use a Raven executable from the same revision as the library linked
into Caravan when checking emitted proofs.

Run the example with:

```sh
dune build @test/examples/module_ms_queue/runtest
```
