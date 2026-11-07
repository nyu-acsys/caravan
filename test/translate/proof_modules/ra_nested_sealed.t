  $ caravan --shh ra_nested_sealed.ml
  Verification successful.
  $ caravan --shh --emit-rav ra_nested_sealed.ml > ra_nested_sealed.rav
  $ raven --shh ra_nested_sealed.rav
  Verification successful.
