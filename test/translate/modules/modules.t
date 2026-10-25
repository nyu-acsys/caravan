  $ caravan --shh modules.ml
  Verification successful.

  $ caravan --shh signatures.ml
  Verification successful.

  $ caravan --shh aliases.ml
  Verification successful.

  $ caravan --shh scopes.ml
  Verification successful.

  $ caravan --shh qualified_pure.ml
  Verification successful.

  $ caravan --shh manual.ml
  Verification successful.

  $ caravan --shh --emit-rav qualified_pure.ml > emitted.rav
  $ raven --shh --typeonly emitted.rav
  Verification successful.
