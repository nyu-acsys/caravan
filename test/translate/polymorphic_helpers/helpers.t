Lifted helpers reuse the enclosing function's type dictionaries and ordinary
captured arguments, including recursive queue construction.

  $ caravan --shh helpers.ml
  Verification successful.
  $ caravan --shh --emit-rav helpers.ml > helpers.rav
  $ raven --shh helpers.rav
  Verification successful.

Capture-free generalized helpers reuse the ordinary generic worker mechanism.

  $ caravan --shh generalized.ml
  Verification successful.
  $ caravan --shh --emit-rav generalized.ml > generalized.rav
  $ raven --shh generalized.rav
  Verification successful.
