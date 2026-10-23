  $ caravan --shh manual_state_bad_result_fail.ml
  [Error] File "manual_state_bad_result_fail.ml", line 4, columns 4-24:
  4 |     (result + 1, result)) *)
          ^^^^^^^^^^^^^^^^^^^^
  Type Error: A stateful scope must return (unchanged operation result, output state).
  [1]
