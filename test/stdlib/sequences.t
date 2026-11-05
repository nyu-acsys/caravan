Finite snapshots are reusable and their contents retain their source types.

  $ caravan --shh sequences.ml
  Verification successful.
  $ caravan --shh --emit-rav sequences.ml > sequences.rav
  $ raven --shh sequences.rav
  Verification successful.

Traversal requires a snapshot capability, and construction preserves opaque identities.

  $ caravan --shh sequence_unowned.ml > unowned.out 2>&1
  [1]
  $ grep -c 'A precondition may not hold for this call' unowned.out
  1
  $ ! grep -qi 'timed out' unowned.out
  $ caravan --shh sequence_identity.ml > identity.out 2>&1
  [1]
  $ grep -c 'A postcondition may not hold' identity.out
  1
  $ ! grep -qi 'timed out' identity.out

Structural equality and direct thunk invocation remain unsupported.

  $ caravan --shh sequence_equality.ml > equality.out 2>&1
  [1]
  $ grep -c 'Structural equality on values containing references is unsupported' equality.out
  1
  $ caravan --shh sequence_force.ml > force.out 2>&1
  [1]
  $ grep -c 'Unsupported Error:' force.out
  1
