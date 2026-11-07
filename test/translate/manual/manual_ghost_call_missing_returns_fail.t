  $ caravan --shh manual_ghost_call_missing_returns_fail.ml
  [Error] File "manual_ghost_call_missing_returns_fail.ml", line 1, columns 29-34:
  1 | let identity (value : int) = value
                                   ^^^^^
  Type Error: A normal return with ghost results needs Ghost.returns.
  [1]
