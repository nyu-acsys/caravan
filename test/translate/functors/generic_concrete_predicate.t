Generic module predicates accept a concrete element type in an invariant body.

  $ caravan --shh generic_concrete_predicate.ml
  Verification successful.
  $ caravan --shh --emit-rav generic_concrete_predicate.ml > generic_concrete_predicate.rav
  $ raven --shh generic_concrete_predicate.rav
  Verification successful.
