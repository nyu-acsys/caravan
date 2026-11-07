  $ caravan --shh client.ml
  Verification successful.

  $ caravan --shh --emit-rav client.ml > emitted.rav
  $ raven --shh --typeonly emitted.rav
  Verification successful.
