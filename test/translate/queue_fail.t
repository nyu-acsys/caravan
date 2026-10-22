  $ caravan --shh queue_fail.ml
  [Error] File "queue_fail.ml", line 10, columns 9-56:
  10 |       if Atomic.compare_and_set q.head old_head old_head then Some value else pop_opt q
                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This step may not perform the action pop.
  [Error] File "queue_fail.ml", line 16, columns 49-49:
  16 |   if Atomic.compare_and_set q.tail old_tail fresh then () else ()
                                                        ^
  Verification Error: The invariant is_queue may not hold after this step.
  File "queue_fail.proof", line 10, columns 10-18:
  10 | invariant is_queue (q : t) (s : state) =
                 ^^^^^^^^
  Related Location: The invariant.
  [1]
