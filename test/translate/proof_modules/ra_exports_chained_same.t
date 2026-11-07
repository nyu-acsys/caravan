  $ caravan --shh ra_exports_chained_same.ml
  Verification successful.
  $ caravan --shh --emit-rav ra_exports_chained_same.ml > ra_exports_chained_same.rav
  $ raven --shh ra_exports_chained_same.rav
  Verification successful.
