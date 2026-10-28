Pure functor functions work without an algebraic ghost type.

  $ caravan --shh models_functions.ml
  Verification successful.
  $ caravan --shh --emit-rav models_functions.ml > models_functions.rav
  $ raven --shh models_functions.rav
  Verification successful.
