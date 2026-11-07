Parameterized proof variants and records retain mathematical payload types.

  $ caravan --shh types.ml
  Verification successful.
  $ caravan --shh --emit-rav types.ml > types.rav
  $ raven --shh types.rav
  Verification successful.
