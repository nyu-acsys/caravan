Task signature inference recognizes local pure functions, logical functions, and scoped predicates.

  $ caravan --shh ghost_predicate.ml
  Verification successful.
  $ caravan --shh --emit-rav ghost_predicate.ml > ghost_predicate.rav
  $ raven --shh ghost_predicate.rav
  Verification successful.
