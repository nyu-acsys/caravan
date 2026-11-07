  $ caravan --shh -I ra_exports_lib ra_implicit_empty.ml
  Verification successful.
  $ caravan --shh -I ra_exports_lib --emit-rav ra_implicit_empty.ml > ra_implicit_empty.rav
  $ raven --shh ra_implicit_empty.rav
  Verification successful.
