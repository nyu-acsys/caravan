Ghost ownership preserves the element type of reference values.

  $ caravan --shh ghost_storage_ownership_type_fail.ml
  [Error] File "ghost_storage_ownership_type_fail.proof", line 4, columns 41-46:
  4 |   requires (own (Ghost.at watched owner) value) = ()
                                               ^^^^^
  Type Error: The value value has type bool ref but an expression was expected of type
    int ref
  Type bool is not compatible with type int.
  [1]
