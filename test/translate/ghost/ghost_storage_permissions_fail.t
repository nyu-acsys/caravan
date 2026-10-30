Ghost storage operations require sufficient ownership and valid initial resources.

  $ caravan --shh ghost_storage_permissions_fail.ml
  [Error] File "ghost_storage_permissions_fail.proof", line 8, columns 2-39:
  8 |   Ghost.write (Ghost.at flag cell) true
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Could not assert sufficient permissions to assign this field.
  [Error] File "ghost_storage_permissions_fail.proof", line 11, columns 14-32:
  11 |   Ghost.read (Ghost.at flag cell)
                     ^^^^^^^^^^^^^^^^^^
  Verification Error: Could not assert sufficient permissions to access this field.
  [Error] File "ghost_storage_permissions_fail.proof", line 14, columns 2-46:
  14 |   Ghost.alloc [Ghost.init facts Authority.top]
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Could not prove validity of initially-allocated value.
  [1]
