Combining independent local generalization with captured outer type parameters
remains explicitly guarded.

  $ caravan --shh mixed.ml > mixed.out 2>&1
  [1]
  $ grep -q 'Generalized local functions with captured type parameters' mixed.out
  $ ! grep -q 'Internal Error:' mixed.out

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
