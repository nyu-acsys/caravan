Frozen reads use a separate checked contract selected by a scope wrapper.
Visibility is indexed by the executing owner and survives procedure contracts.

  $ caravan --shh frozen_reads.ml
  Verification successful.
  $ caravan --shh --emit-rav frozen_reads.ml > frozen_reads.rav
  $ raven --shh frozen_reads.rav
  Verification successful.

A frozen fact alone and evidence for a foreign owner cannot authorize a read.

  $ caravan --shh frozen_read_missing_fail.ml > missing.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' missing.out
  $ caravan --shh frozen_read_foreign_fail.ml > foreign.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' foreign.out

The wrapper applies only to ordinary Frozen field reads. In particular it
cannot discard a proof attached to an immutable projection or an atomic call.

  $ caravan --shh frozen_read_ordinary_fail.ml > ordinary.out 2>&1
  [1]
  $ grep -q 'Ghost.frozen_scope requires a Frozen field' ordinary.out
  $ caravan --shh frozen_read_immutable_fail.ml > immutable.out 2>&1
  [1]
  $ grep -q 'Ghost.scope must follow an ordinary field access' immutable.out
  [1]
  $ caravan --shh frozen_read_atomic_fail.ml > atomic.out 2>&1
  [1]
  $ grep -q 'This scope does not match the attached operation' atomic.out
