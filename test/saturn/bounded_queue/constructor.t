The list constructor establishes a queue whose later operations obey the exact
capacity and FIFO contracts, including zero and default capacity.

  $ cat bounded_queue.ml constructor_clients.ml > constructors.ml
  $ cat bounded_queue.proof constructor_clients.proof > constructors.proof
  $ caravan --shh -I ../backoff --only of_list_exn constructors.ml
  Verification successful.
  $ caravan --shh -I ../backoff --only Constructor_clients constructors.ml
  Verification successful.
