History witnesses cross spawned tasks and returned handles before an ordinary call.

  $ caravan --shh history.ml
  Verification successful.
  $ caravan --shh --history=monotone history.ml
  Verification successful.
  $ caravan --shh --emit-rav history.ml > history.rav
  $ raven --shh history.rav
  Verification successful.
