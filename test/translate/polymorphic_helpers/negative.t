Independent local and captured type parameters cannot be cast to one another.

  $ caravan --shh mixed_cast.ml > mixed_cast.out 2>&1
  [1]
  $ grep -q 'Type Error:' mixed_cast.out
  $ ! grep -q 'Internal Error:' mixed_cast.out

Helper annotations cannot specialize an enclosing universally quantified type.

  $ caravan --shh specializing.ml > specializing.out 2>&1
  [1]
  $ grep -q 'Type Error:' specializing.out
  $ ! grep -q 'Internal Error:' specializing.out

Captured arguments do not justify false helper contracts.

  $ caravan --shh bad_contract.ml > bad_contract.out 2>&1
  [1]
  $ grep -q 'Verification Error:' bad_contract.out
  $ ! grep -q 'Internal Error:' bad_contract.out
