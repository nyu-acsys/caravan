A generic field index cannot conflate integer and Boolean contents.

  $ caravan --shh field_type_fail.ml > field_type_fail.out 2>&1
  [1]
  $ grep -q 'consistent type parameters for this ghost field' field_type_fail.out
  $ ! grep -q 'Internal Error:' field_type_fail.out
