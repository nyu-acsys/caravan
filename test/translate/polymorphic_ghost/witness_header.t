Witness-selected results do not constrain a helper's inferred ghost header types.

  $ caravan --shh witness_header.ml
  Verification successful.

  $ caravan --shh --emit-rav witness_header.ml > emitted.rav
  $ raven --shh --typeonly emitted.rav
  Verification successful.
