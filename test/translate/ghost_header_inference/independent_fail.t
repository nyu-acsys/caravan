Ghost annotations cannot unify independently generalized native parameters.

  $ caravan --shh independent_fail.ml > independent_fail.out 2>&1
  [1]
  $ grep -q 'Type Error:' independent_fail.out
  $ ! grep -q 'Internal Error:' independent_fail.out
  $ ! grep -q 'Assertion failed' independent_fail.out
