  $ caravan --shh --smt-timeout=30000 queue_fail.ml
  [Error] File "queue_fail.ml", line 10, columns 9-56:
  10 |       if Atomic.compare_and_set q.head old_head old_head then Some value else pop_opt q
                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This step may not perform the action pop.
  [Error] File "queue_fail.ml", line 16, columns 5-49:
  16 |   if Atomic.compare_and_set q.tail old_tail fresh then () else ()
            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This step may change the state of is_queue in a way that no action allows; if it performs one, say so, as (*@ performs a *).
  File "queue_fail.proof", line 12, columns 10-18:
  12 | invariant is_queue (q : t) (s : state) =
                 ^^^^^^^^
  Related Location: The invariant.
  [Error] File "queue_fail.ml", line 22, column 4 to line 25, column 68:
  22 |     (Atomic.get
           ^^^^^^^^^^^
  Verification Error: The atomic postcondition may not hold after this step, which linearizes the function.
  File "queue_fail.mli", line 19, columns 19-52:
  19 |     atomic ensures queue q xs && b = (length xs = 0) *)
                          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: The atomic postcondition.
  [Error] File "queue_fail.ml", line 22, column 4 to line 25, column 68:
  22 |     (Atomic.get
           ^^^^^^^^^^^
  Verification Error: A postcondition may not hold at this return point.
  File "queue_fail.mli", line 19, columns 33-52:
  19 |     atomic ensures queue q xs && b = (length xs = 0) *)
                                        ^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
