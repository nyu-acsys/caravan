Resource fields require frame-preserving updates.

  $ caravan --shh ghost_storage_write_resource_fail.ml
  [Error] File "ghost_storage_write_resource_fail.proof", line 8, columns 15-35:
  8 |   Ghost.write (Ghost.at facts owner) (Authority.full (Facts.set Set.empty))
                     ^^^^^^^^^^^^^^^^^^^^
  Type Error: Ghost.read and Ghost.write require an ordinary value field.
  [1]
