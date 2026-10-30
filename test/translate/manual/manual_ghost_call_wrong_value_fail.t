  $ caravan --shh manual_ghost_call_wrong_value_fail.ml
  [Error] File "manual_ghost_call_wrong_value_fail.ml", line 1, columns 34-34:
  1 | let identity (value : int) = value
                                        ^
  Verification Error: A postcondition may not hold at this return point.
  File "manual_ghost_call_wrong_value_fail.ml", line 5, columns 12-25:
  5 |     ensures result = copy && copy = value *)
                  ^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
