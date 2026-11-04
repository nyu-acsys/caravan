  $ caravan --shh -I ../backoff --smt-timeout=30000 michael_scott_queue.ml
  Verification successful.
  $ caravan --shh --history=monotone -I ../backoff --smt-timeout=30000 michael_scott_queue.ml
  Verification successful.

The emitted history proof, including its dynamic initializer, is standalone Raven.

  $ caravan --shh -I ../backoff --emit-rav michael_scott_queue.ml > emitted.rav
  $ raven --shh --typeonly emitted.rav
  Verification successful.

Clients use the polymorphic interface for empty, singleton, longer and mixed integer/boolean
queues, and a generic round trip.

  $ mkdir client
  $ cp michael_scott_queue.mli of_list_client.ml client/
  $ caravan --shh -I ../backoff client/of_list_client.ml
  Verification successful.

Incorrect initial contents fail at the exposing lemma's precondition.

  $ mkdir wrong_contents
  $ cp michael_scott_queue.mli michael_scott_queue.proof wrong_contents/
  $ sed 's/build_next list/build_next []/' michael_scott_queue.ml > wrong_contents/michael_scott_queue.ml
  $ caravan --shh -I ../backoff --smt-timeout=30000 wrong_contents/michael_scott_queue.ml
  [Error] File "wrong_contents/michael_scott_queue.ml", line 147, columns 18-61:
  147 |   let cell_list = expose_built_chain (Some q.head) tail_ list in
                          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: A precondition may not hold for this call.
  File "wrong_contents/michael_scott_queue.proof", line 75, columns 29-64:
  75 |   requires (own limit Nil && built_chain first limit items cells)
                                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]

The builder must return its designated terminal cell.

  $ mkdir wrong_terminal
  $ cp michael_scott_queue.mli michael_scott_queue.proof wrong_terminal/
  $ sed 's/| \[\] -> tail_/| [] -> Atomic.make (Atomic.get tail_)/' michael_scott_queue.ml > wrong_terminal/michael_scott_queue.ml
  $ caravan --shh -I ../backoff --smt-timeout=30000 wrong_terminal/michael_scott_queue.ml
  [Error] File "wrong_terminal/michael_scott_queue.ml", line 139, columns 13-40:
  139 |     (*@ fold built_chain result tail_ xs *)
                     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  File "wrong_terminal/michael_scott_queue.proof", line 46, columns 10-24:
  46 |   | [] -> first == limit && cells === [limit]
                 ^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
