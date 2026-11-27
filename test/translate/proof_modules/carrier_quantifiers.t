Mathematical record quantifiers cover the full carrier of an abstract key type.

  $ caravan --shh carrier_quantifiers.ml
  Verification successful.

Flattening a universal mathematical record does not introduce machine bounds.

  $ caravan --shh carrier_quantifiers_bounds.ml > bounds.out 2>&1
  [1]
  $ grep -q 'Verification Error: A postcondition may not hold' bounds.out
  $ grep -qi 'timeout' bounds.out
  [1]
