  $ caravan --shh ra_exports_mli.ml
  Verification successful.
  $ caravan --shh --emit-rav ra_exports_mli.ml > ra_exports_mli.rav
  $ raven --shh ra_exports_mli.rav
  Verification successful.
