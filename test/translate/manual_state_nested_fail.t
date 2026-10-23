  $ caravan --shh manual_state_nested_fail.ml
  [Error] File "manual_state_nested_fail.ml", line 5, column 7 to line 7, column 27:
  5 |        (*@ Ghost.State.scope (fun step () ->
             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: A stateful scope needs a direct let binding, sequence continuation, or lexical tail.
  [1]
