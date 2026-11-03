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

Generalized helpers retain independent argument dictionaries and captured lexical
dictionaries, including captures absent from the helper's native arrow type.

  $ caravan --shh mixed.ml
  Verification successful.
  $ caravan --shh --emit-rav mixed.ml > mixed.rav
  $ raven --shh mixed.rav
  Verification successful.
