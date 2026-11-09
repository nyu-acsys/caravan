Generic records share fields with concrete clients and preserve field ownership.

  $ caravan --shh records.ml
  Verification successful.
  $ caravan --shh --emit-rav records.ml > records.rav
  $ raven --shh records.rav
  Verification successful.
  $ caravan --shh functors.ml
  Verification successful.
  $ caravan --shh --emit-rav functors.ml > functors.rav
  $ raven --shh functors.rav
  Verification successful.
  $ caravan --shh api.ml
  Verification successful.
  $ mkdir imported
  $ cp api.mli imported/api.mli
  $ caravan --shh -I imported client.ml
  Verification successful.

Missing ownership, fractional writes, incorrect values and incompatible payloads fail.

  $ caravan --shh no_ownership_fail.ml > no_ownership.out 2>&1
  [1]
  $ grep -F 'Verification Error: A precondition may not hold for this call.' no_ownership.out
  Verification Error: A precondition may not hold for this call.
  $ caravan --shh fractional_write_fail.ml > fractional_write.out 2>&1
  [1]
  $ grep -F 'Verification Error: A precondition may not hold for this call.' fractional_write.out
  Verification Error: A precondition may not hold for this call.
  $ caravan --shh wrong_value_fail.ml > wrong_value.out 2>&1
  [1]
  $ grep -F 'Verification Error: A postcondition may not hold at this return point.' wrong_value.out
  Verification Error: A postcondition may not hold at this return point.
  $ caravan --shh type_bounds_fail.ml > type_bounds.out 2>&1
  [1]
  $ grep -o 'Type Error:' type_bounds.out
  Type Error:

Structural equality of parameterized heap records still requires heap reads.

  $ caravan --shh equality_fail.ml > equality.out 2>&1
  [1]
  $ grep -o 'Structural equality on values containing references is unsupported' equality.out
  Structural equality on values containing references is unsupported
