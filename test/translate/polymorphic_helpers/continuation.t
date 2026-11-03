Continuation contracts restrict a generalized helper to the enclosing payload type.
The checked helper shares the owner's worker and dictionaries.

  $ caravan --shh continuation.ml
  Verification successful.
  $ caravan --shh --emit-rav continuation.ml > continuation.rav
  $ raven --shh continuation.rav
  Verification successful.

An OCaml-valid call at an unrelated payload type cannot use the restricted contract.

  $ mkdir invalid_continuation
  $ cp continuation.mli continuation.proof invalid_continuation/
  $ sed 's/helper q value/helper (Atomic.make 0) 0/' continuation.ml > invalid_continuation/continuation.ml
  $ caravan --shh invalid_continuation/continuation.ml > invalid.out 2>&1
  [1]
  $ grep -q "This call does not satisfy the helper's continuation type instance" invalid.out
  $ ! grep -q 'Internal Error:' invalid.out
