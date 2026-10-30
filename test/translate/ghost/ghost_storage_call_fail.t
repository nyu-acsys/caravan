An allocation inside an argument does not make the enclosing call fresh.

  $ caravan --shh ghost_storage_call_fail.ml
  [Error] File "ghost_storage_call_fail.ml", line 6, columns 4-45:
  6 |     (*@ initializes [Ghost.init tag false] *)
          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: This annotation must follow a fresh allocation.
  [1]
