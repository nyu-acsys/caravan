Ghost initializers preserve the element type of reference values.

  $ caravan --shh ghost_storage_initializer_type_fail.ml
  [Error] File "ghost_storage_initializer_type_fail.ml", line 5, columns 40-45:
  5 |     (*@ initializes [Ghost.init watched value] *)
                                              ^^^^^
  Type Error: The value value has type bool ref but an expression was expected of type
    int ref
  Type bool is not compatible with type int.
  [1]
