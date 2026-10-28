An imported signature preserves root, nested, and named algebra carriers.

  $ caravan --shh -I ra_exports_lib ra_exports_imported.ml
  Verification successful.
  $ caravan --shh -I ra_exports_lib --emit-rav ra_exports_imported.ml > ra_exports_imported.rav
  $ raven --shh ra_exports_imported.rav
  Verification successful.
