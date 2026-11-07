  $ caravan --shh -I ra_exports_lib ra_implicit_no_proof.ml
  Verification successful.
  $ caravan --shh -I ra_exports_lib --emit-rav ra_implicit_no_proof.ml > ra_implicit_no_proof.rav
  $ raven --shh ra_implicit_no_proof.rav
  Verification successful.
