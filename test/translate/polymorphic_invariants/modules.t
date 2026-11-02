Module aliases retain the invariant and view identities for each inferred payload type.

  $ caravan --shh modules.ml
  Verification successful.
  $ caravan --shh --emit-rav modules.ml > modules.rav
  $ raven --shh modules.rav
  Verification successful.
