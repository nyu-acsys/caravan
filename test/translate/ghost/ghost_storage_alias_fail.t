Ghost initializers require an allocation expression.

  $ caravan --shh ghost_storage_alias_fail.ml
  [Error] File "ghost_storage_alias_fail.ml", line 5, columns 4-45:
  5 |     (*@ initializes [Ghost.init tag false] *)
          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: This annotation must follow a fresh allocation.
  [1]
