The generic segment predicate and structural lemmas use the ordinary ownership
proof translation at integer and boolean instantiations.

  $ caravan --shh segment.ml
  Verification successful.
  $ caravan --shh --emit-rav segment.ml > segment.rav
  $ raven --shh segment.rav
  Verification successful.
