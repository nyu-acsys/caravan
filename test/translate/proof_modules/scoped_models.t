Nested logical models resolve ancestor and sibling names, aliases, and flattened-name collisions.

  $ caravan --shh scoped_models.ml
  Verification successful.
  $ caravan --shh --emit-rav scoped_models.ml > scoped_models.rav
  $ raven --shh scoped_models.rav
  Verification successful.
