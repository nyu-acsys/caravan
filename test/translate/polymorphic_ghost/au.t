Explicit atomic-update contexts preserve their type indices through binding, abort,
commit, ghost state, and token fields.

  $ caravan --shh au.ml
  Verification successful.
  $ caravan --shh --emit-rav au.ml > au.rav
  $ raven --shh au.rav
  Verification successful.
