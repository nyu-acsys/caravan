  $ caravan --shh treiber_stack_fail.ml
  [Error] File "treiber_stack_fail.ml", line 9, columns 17-29:
  9 | let is_empty t = Atomic.get t (*@ commit *) != []
                       ^^^^^^^^^^^^
  Verification Error: The atomic postcondition may not hold after this step, which linearizes the function.
  File "treiber_stack_fail.mli", line 14, columns 19-46:
  14 |     atomic ensures b = (xs = []) && stack t xs *)
                          ^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: The atomic postcondition.
  [Error] File "treiber_stack_fail.ml", line 9, columns 17-29:
  9 | let is_empty t = Atomic.get t (*@ commit *) != []
                       ^^^^^^^^^^^^
  Verification Error: A postcondition may not hold at this return point.
  File "treiber_stack_fail.mli", line 14, columns 19-32:
  14 |     atomic ensures b = (xs = []) && stack t xs *)
                          ^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [Error] File "treiber_stack_fail.ml", line 14, columns 9-49:
  14 |   if not (Atomic.compare_and_set t before before) then push t value
                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: The atomic postcondition may not hold after this step, which linearizes the function.
  File "treiber_stack_fail.mli", line 19, columns 19-36:
  19 |     atomic ensures stack t (v :: xs) *)
                          ^^^^^^^^^^^^^^^^^
  Related Location: This part of the atomic postcondition may not hold.
  [1]
