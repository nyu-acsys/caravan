  $ caravan --shh manual_ghost_call_wrong_outputs_fail.ml
  [Error] File "manual_ghost_call_wrong_outputs_fail.ml", line 2, columns 36-52:
  2 | (*@ Ghost.returns (fun result () -> (result, result)) *)
                                          ^^^^^^^^^^^^^^^^
  Type Error: This expression has type 'a * 'b but an expression was expected of type int.
  [1]
