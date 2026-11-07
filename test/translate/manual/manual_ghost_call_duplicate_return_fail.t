  $ caravan --shh manual_ghost_call_duplicate_return_fail.ml
  [Error] File "manual_ghost_call_duplicate_return_fail.ml", line 2, columns 0-46:
  2 | (*@ Ghost.returns (fun result () -> result) *)
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: This expression has more than one annotation of this kind.
  [1]
