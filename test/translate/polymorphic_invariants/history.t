Generic growing states preserve typed history witnesses across calls, including
integer and boolean instances held simultaneously by one caller.

  $ caravan --shh history.ml
  Verification successful.
  $ caravan --shh --history=monotone history.ml
  Verification successful.
  $ caravan --shh --emit-rav history.ml > history.rav
  $ raven --shh history.rav
  Verification successful.
