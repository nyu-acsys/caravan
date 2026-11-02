Direct invariants share one generic body and distinguish payload types in one caller.

  $ caravan --shh direct.ml
  Verification successful.
  $ caravan --shh --emit-rav direct.ml > direct.rav
  $ raven --shh direct.rav
  Verification successful.
