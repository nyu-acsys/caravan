Shared function workers capture opaque outer module types and operations.
Repeated source applications and module aliases retain those captured identities.

  $ caravan --shh modules_extra.ml
  Verification successful.
  $ caravan --shh --emit-rav modules_extra.ml > modules_extra.rav
  $ raven --shh modules_extra.rav
  Verification successful.
