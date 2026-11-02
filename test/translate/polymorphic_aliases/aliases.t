Transparent type abbreviations substitute their parameters in values, containers,
and atomic storage without introducing additional nominal carriers.

  $ caravan --shh aliases.ml
  Verification successful.
  $ caravan --shh --emit-rav aliases.ml > aliases.rav
  $ raven --shh aliases.rav
  Verification successful.
