Frame-preserving updates require a resource field.

  $ caravan --shh ghost_storage_fpu_value_fail.ml
  [Error] File "ghost_storage_fpu_value_fail.proof", line 5, columns 2-43:
  5 |   Ghost.fpu (Ghost.at tag owner) false true
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: Ghost.fpu requires a resource field.
  [1]
