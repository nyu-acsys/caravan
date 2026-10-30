An initializer list cannot initialize the same ghost field twice.

  $ caravan --shh ghost_storage_duplicate_fail.ml
  [Error] File "ghost_storage_duplicate_fail.ml", line 4, columns 20-63:
  4 |     (*@ initializes [Ghost.init tag false; Ghost.init tag true] *)
                          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: A ghost field is initialized more than once.
  [1]
