  $ caravan --shh manual_state_wrong_input_fail.ml
  [Error] File "manual_state_wrong_input_fail.ml", line 9, columns 33-38:
  9 | (*@ Ghost.State.scope (fun step (saved : bool) ->
                                       ^^^^^
  Type Error: The proof pattern has a different type from its input.
  [1]
