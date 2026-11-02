A local interface can specify a generalized function and concrete clients.

  $ caravan --shh interfaces.ml
  Verification successful.
  $ caravan --shh --emit-rav interfaces.ml > interfaces.rav
  $ raven --shh interfaces.rav
  Verification successful.
