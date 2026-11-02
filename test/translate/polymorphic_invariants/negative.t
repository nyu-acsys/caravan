Generic initialization cannot establish a false state property.

  $ caravan --shh bad_state.ml > bad_state.out 2>&1
  [1]
  $ grep -q 'Verification Error:' bad_state.out
  $ ! grep -q 'Internal Error:' bad_state.out

Alpha-equivalent resource signatures must preserve sharing between all parameters.

  $ caravan --shh bad_sharing.ml > bad_sharing.out 2>&1
  [1]
  $ grep -q 'The module resource has different parameter types' bad_sharing.out
  $ ! grep -q 'Internal Error:' bad_sharing.out
