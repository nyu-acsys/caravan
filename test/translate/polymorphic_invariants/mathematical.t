Parameterized invariant fields and views retain mathematical integer values.

  $ caravan --shh mathematical.ml
  Verification successful.
  $ caravan --shh --emit-rav mathematical.ml > mathematical.rav
  $ raven --shh mathematical.rav
  Verification successful.

A view's mathematical integer component does not acquire runtime bounds.

  $ caravan --shh bad_bound.ml > bad_bound.out 2>&1
  [1]
  $ grep -q 'Verification Error:' bad_bound.out
  $ ! grep -q 'Internal Error:' bad_bound.out
