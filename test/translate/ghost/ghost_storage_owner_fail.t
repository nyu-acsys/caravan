Ghost initializers preserve their field's OCaml owner type.

  $ caravan --shh ghost_storage_owner_fail.ml
  [Error] File "ghost_storage_owner_fail.ml", line 4, columns 32-35:
  4 |     (*@ initializes [Ghost.init tag false] *)
                                      ^^^
  Type Error: This ghost field has a different owner type.
  [1]
