An invariant, token field and atomic operation share one dictionary-indexed family.

  $ caravan --shh cycle.ml
  Verification successful.
  $ caravan --shh --emit-rav cycle.ml > cycle.rav
  $ raven --shh cycle.rav
  Verification successful.
