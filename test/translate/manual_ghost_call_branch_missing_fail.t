  $ caravan --shh manual_ghost_call_branch_missing_fail.ml
  [Error] File "manual_ghost_call_branch_missing_fail.ml", line 2, columns 72-77:
  2 |   if flag then left (*@ Ghost.returns (fun result () -> result) *) else right
                                                                              ^^^^^
  Type Error: A normal return with ghost results needs Ghost.returns.
  [1]
