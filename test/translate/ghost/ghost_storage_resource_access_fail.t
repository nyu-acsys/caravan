Resource fields keep their algebra's ownership semantics.

  $ caravan --shh ghost_storage_read_resource_fail.ml
  [Error] File "ghost_storage_read_resource_fail.proof", line 6, columns 14-33:
  6 |   Ghost.read (Ghost.at facts cell)
                    ^^^^^^^^^^^^^^^^^^^
  Type Error: Ghost.read and Ghost.write require an ordinary value field.
  [1]

  $ caravan --shh ghost_storage_fraction_resource_fail.ml
  [Error] File "ghost_storage_fraction_resource_fail.proof", line 5, columns 12-72:
  5 |   requires (own ~fraction:Permission.half (Ghost.at facts cell) Facts.id) = ()
                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: Resource fields do not take a fractional permission.
  [1]
