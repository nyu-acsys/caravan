A unit expression commits a no-op update. A unit argument does not steal the
annotation attached to its enclosing atomic operation.

  $ caravan --shh unit_commit.ml
  Verification successful.
  $ caravan --shh --emit-rav unit_commit.ml > unit_commit.rav
  $ raven --shh unit_commit.rav
  Verification successful.

A commit at a unit expression cannot change the abstract contents.

  $ mkdir changed
  $ cp unit_commit.ml unit_commit.proof changed/
  $ sed 's/atomic ensures cell c before/atomic ensures cell c 1/' unit_commit.mli > changed/unit_commit.mli
  $ caravan --shh changed/unit_commit.ml > changed.out 2>&1
  [1]
  $ grep -c 'The atomic postcondition may not hold after this step' changed.out
  1
  $ ! grep -qi 'timed out' changed.out
