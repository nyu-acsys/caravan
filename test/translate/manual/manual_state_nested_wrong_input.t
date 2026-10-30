The outer read must accept the inner scope's output type.

  $ caravan --shh manual_state_nested_wrong_input.ml
  [Error] File "manual_state_nested_wrong_input.ml", line 8, columns 33-38:
  8 | (*@ Ghost.State.scope (fun step (saved : bool) ->
                                       ^^^^^
  Type Error: The proof pattern has a different type from its input.
  [1]
