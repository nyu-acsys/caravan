Polymorphic operations of module arguments share dictionary-based implementations
at distinct source types, including independent variables and mutable values.

  $ caravan --shh operations.ml
  Verification successful.
  $ caravan --shh --emit-rav operations.ml > operations.rav
  $ raven --shh operations.rav
  Verification successful.

Atomic contracts retain their implicit contents at each polymorphic call.

  $ caravan --shh atomic.ml
  Verification successful.
  $ caravan --shh --emit-rav atomic.ml > atomic.rav
  $ raven --shh atomic.rav
  Verification successful.
