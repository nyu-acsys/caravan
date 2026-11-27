Immutable heap fields retain exact reads beside frozen and relaxed fields.
Direct projections, record patterns, inline records and generic modules share
one read contract. Immutable reads can borrow ownership from an invariant.

  $ caravan --shh mixed_records.ml
  Verification successful.
  $ caravan --shh --emit-rav mixed_records.ml > mixed_records.rav
  $ grep -q 'atomic proc .*_immutable_read' mixed_records.rav
  $ raven --shh mixed_records.rav
  Verification successful.

Immutable reads still require ownership. Reading a stored Atomic.t reference
alone does not acquire visibility of that atomic's contents or other fields.

  $ caravan --shh mixed_missing_fail.ml > missing.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' missing.out
  $ grep -qi 'timeout' missing.out
  [1]
  $ caravan --shh mixed_no_acquire_fail.ml > acquire.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' acquire.out
  $ grep -qi 'timeout' acquire.out
  [1]
  $ caravan --shh mixed_distinct_fail.ml > distinct.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' distinct.out
  $ grep -qi 'timeout' distinct.out
  [1]

Ordinary mutable fields retain their existing visibility-mode restriction.

  $ caravan --shh mixed_mutable_fail.ml > mutable.out 2>&1
  [1]
  $ grep -q 'Shared-field memory encoding is not yet supported for ordinary field reads' mutable.out

The bounded queue's constructor-set indexed inline layout uses the same slots.

  $ caravan --shh mixed_indexed.ml
  Verification successful.
  $ caravan --shh --emit-rav mixed_indexed.ml > mixed_indexed.rav
  $ raven --shh mixed_indexed.rav
  Verification successful.
