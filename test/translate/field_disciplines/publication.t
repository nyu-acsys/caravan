Publication lower bounds survive contracts. Receivers obtain visibility through
a real atomic read, including when the channel and payload have different types.

  $ caravan --shh publication.ml
  Verification successful.
  $ caravan --shh publication_generic.ml
  Verification successful.
  $ caravan --shh --emit-rav publication.ml > publication.rav
  $ raven --shh publication.rav
  Verification successful.

Coverage alone cannot acquire visibility, and an unrelated channel cannot
supply the required release bound.

  $ caravan --shh publication_missing_acquire_fail.ml > missing.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' missing.out
  $ caravan --shh publication_wrong_channel_fail.ml > channel.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' channel.out
  $ caravan --shh publication_foreign_release_fail.ml > foreign.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' foreign.out

Ordinary ownership cannot manufacture an arbitrary release lower bound.
The scope must match the physical operation.

  $ caravan --shh publication_forged_bound_fail.ml > forged.out 2>&1
  [1]
  $ grep -q 'A postcondition may not hold' forged.out
  $ caravan --shh publication_wrong_scope_fail.ml > scope.out 2>&1
  [1]
  $ grep -q 'This publication scope does not match the atomic operation' scope.out

A failed CAS cannot publish a newly supplied lower bound.

  $ caravan --shh publication_failed_cas_fail.ml > cas.out 2>&1
  [1]
  $ grep -q 'A postcondition may not hold' cas.out
