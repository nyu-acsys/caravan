Annotations cannot identify independently quantified proof types.

  $ caravan --shh wrong_cast.ml > wrong_cast.out 2>&1
  [1]
  $ grep -q 'Type Error:' wrong_cast.out
  $ ! grep -q 'Internal Error:' wrong_cast.out
