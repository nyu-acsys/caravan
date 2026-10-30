  $ caravan --shh manual_ghost_call_pre_result_fail.ml
  [Error] File "manual_ghost_call_pre_result_fail.ml", line 4, columns 50-62:
  4 | (*@ result, [copy : int] = invalid value requires copy = value ensures copy = result *)
                                                        ^^^^^^^^^^^^
  Type Error: The ghost result copy is unavailable in a precondition.
  [1]
