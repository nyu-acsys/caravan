Opening a direct invariant across a call with two writes is rejected.

  $ caravan --shh manual_ghost_call_non_atomic_fail.ml
  [Error] File "manual_ghost_call_non_atomic_fail.ml", line 16, columns 44-59:
  16 | let under_invariant (cell : int Atomic.t) = two_writes cell
                                                   ^^^^^^^^^^^^^^^
  Verification Error: Cannot take a non-atomic step while an invariant or atomic update is open.
  [1]
