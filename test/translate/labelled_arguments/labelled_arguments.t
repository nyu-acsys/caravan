Fully supplied labelled arguments use the existing positional translation,
including reordered labels, patterns, aliases, pure functions and generic modules.

  $ caravan --shh functions.ml
  Verification successful.
  $ caravan --shh modules.ml
  Verification successful.
  $ caravan --shh --emit-rav modules.ml > modules.rav
  $ raven --shh modules.rav
  Verification successful.
  $ caravan --shh -I imports imports.ml
  Verification successful.

Optional parameters and calls retain their option-valued input slots.

  $ caravan --shh optional.ml
  Verification successful.
  $ caravan --shh -I imports optional_call.ml
  Verification successful.
