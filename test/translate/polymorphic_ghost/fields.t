Ghost fields preserve the stored type across runtime and mathematical callers.

  $ caravan --shh fields.ml
  Verification successful.
  $ caravan --shh --emit-rav fields.ml > fields.rav
  $ raven --shh fields.rav
  Verification successful.
