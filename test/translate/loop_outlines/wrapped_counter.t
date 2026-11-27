Loop invariants carry a spatial predicate's changing value without retaining its initial value.

  $ caravan --shh wrapped_counter.ml
  Verification successful.
  $ caravan --shh --emit-rav wrapped_counter.ml > wrapped_counter.rav
  $ raven --shh wrapped_counter.rav
  Verification successful.
