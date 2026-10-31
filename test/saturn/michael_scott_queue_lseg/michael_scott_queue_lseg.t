  $ caravan --shh -I ../backoff --smt-timeout=30000 michael_scott_queue_lseg.ml
  Verification successful.

The emitted proof parses and type-checks as standalone Raven.

  $ caravan --shh -I ../backoff --emit-rav michael_scott_queue_lseg.ml > emitted.rav
  $ raven --shh --typeonly emitted.rav
  Verification successful.

Clients initialize empty, singleton, and longer queues and exercise FIFO operations.

  $ mkdir client
  $ cp michael_scott_queue_lseg.mli of_list_client.ml client/
  $ caravan --shh -I ../backoff client/of_list_client.ml
  Verification successful.

Building an empty chain cannot establish the input contents.

  $ mkdir wrong_contents
  $ cp michael_scott_queue_lseg.mli michael_scott_queue_lseg.proof wrong_contents/
  $ sed 's/build_next list/build_next []/' michael_scott_queue_lseg.ml > wrong_contents/michael_scott_queue_lseg.ml
  $ caravan --shh -I ../backoff --smt-timeout=30000 wrong_contents/michael_scott_queue_lseg.ml
  [Error] File "wrong_contents/michael_scott_queue_lseg.ml", line 640, columns 10-45:
  640 | (*@ proof initialize_built_queue q tail_ list *)
                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: A precondition may not hold for this call.
  File "wrong_contents/michael_scott_queue_lseg.proof", line 446, columns 7-43:
  446 |     && segment root last values cells edges
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]

The builder must return the owned terminal cell at the end of the chain.

  $ mkdir wrong_terminal
  $ cp michael_scott_queue_lseg.mli michael_scott_queue_lseg.proof wrong_terminal/
  $ sed 's/| \[\] -> tail_/| [] -> let _ = tail_ in Atomic.make Nil/' michael_scott_queue_lseg.ml > wrong_terminal/michael_scott_queue_lseg.ml
  $ caravan --shh -I ../backoff --smt-timeout=30000 wrong_terminal/michael_scott_queue_lseg.ml
  [Error] File "wrong_terminal/michael_scott_queue_lseg.ml", line 628, columns 17-66:
  628 |     | [] -> fold segment result tail_ [] Finset.empty Finset.empty
                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  File "wrong_terminal/michael_scott_queue_lseg.proof", line 8, columns 14-28:
  8 |       | [] -> first == limit && cells = Finset.empty && edges = Finset.empty
                    ^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
