Runtime boundaries preserve admissibility through compound values and mutable storage.
Source quantifiers use the same domain, while proof mathematics stays unrestricted.

  $ caravan --shh compound.ml
  Verification successful.
  $ caravan --shh --emit-rav compound.ml > compound.rav
  $ raven --shh compound.rav
  Verification successful.
  $ caravan --shh empty.ml
  Verification successful.
  $ caravan --shh --emit-rav empty.ml > empty.rav
  $ raven --shh empty.rav
  Verification successful.
  $ caravan --shh ghost_math.ml
  Verification successful.

A raw logical application outside the input domain gains no result-bound guarantee.

  $ caravan --shh invalid_pure_result.ml > invalid_pure_result.out 2>&1
  [1]
  $ grep -q 'Verification Error:' invalid_pure_result.out
  $ ! grep -q 'Internal Error:' invalid_pure_result.out

The representation's default does not produce a source-level empty-type witness.

  $ caravan --shh empty_witness.ml > empty_witness.out 2>&1
  [1]
  $ grep -q 'Verification Error:' empty_witness.out
  $ ! grep -q 'Internal Error:' empty_witness.out

Unsupported large literal syntax produces a source diagnostic.

  $ caravan --shh oversized_literal.ml > oversized_literal.out 2>&1
  [1]
  $ grep -q 'integer literal is outside the supported OCaml int range' oversized_literal.out
  $ ! grep -q 'Internal Error:' oversized_literal.out

An out-of-range element cannot witness a source-level list quantifier.

  $ caravan --shh invalid_compound_witness.ml > invalid_compound_witness.out 2>&1
  [1]
  $ grep -q 'Verification Error:' invalid_compound_witness.out
  $ ! grep -q 'Internal Error:' invalid_compound_witness.out
