  $ caravan --shh manual_state_leak_fail.ml
  [Error] File "manual_state_leak_fail.ml", line 10, columns 33-39:
  10 | (*@ Ghost.State.scope (fun step (leaked : int) ->
                                        ^^^^^^
  Type Error: The proof pattern has a different type from its input.
  [1]
