A generic past-write journal provides persistent provenance without granting
payload ownership. The checked protocol validates speculative reads after a
head check. This is an abstract memory experiment, not a Caravan translation mode.

  $ cat past_writes.rav payload.rav > checked.rav
  $ raven --shh checked.rav
  Verification successful.

Removing validation or permitting a head identity to return invalidates the proof.

  $ sed 's/accepted := !moved_now;/accepted := true;/' checked.rav > unchecked.rav
  $ raven --shh unchecked.rav > unchecked.out 2>&1
  [1]
  $ grep -c '^Verification Error: This assertion may be violated.' unchecked.out
  1
  $ sed 's/val allow_aba: Bool = false/val allow_aba: Bool = true/' checked.rav > aba.rav
  $ raven --shh aba.rav > aba.out 2>&1
  [1]
  $ grep -c '^Verification Error: This assertion may be violated.' aba.out
  1

Stale observations remain possible after a clear. Without an acquire lower
bound, the unrestricted history model also permits earlier private values.

  $ cat checked.rav stale_read_fail.rav > stale.rav
  $ raven --shh stale.rav > stale.out 2>&1
  [1]
  $ grep -c '^Verification Error: This assertion may be violated.' stale.out
  1
  $ cat checked.rav unpublished_counter_fail.rav > counter.rav
  $ raven --shh counter.rav > counter.out 2>&1
  [1]
  $ grep -c '^Verification Error: This assertion may be violated.' counter.out
  1

Unvalidated data does not establish payload validity. Provenance duplication does
not duplicate linear ownership, and clearing requires retirement evidence.

  $ cat checked.rav unchecked_read_fail.rav > invalid.rav
  $ raven --shh invalid.rav > invalid.out 2>&1
  [1]
  $ grep -c '^Verification Error: A postcondition may not hold' invalid.out
  1
  $ cat checked.rav ownership_fail.rav > ownership.rav
  $ raven --shh ownership.rav > ownership.out 2>&1
  [1]
  $ grep -c '^Verification Error: A postcondition may not hold' ownership.out
  1
  $ cat checked.rav early_clear_fail.rav > early.rav
  $ raven --shh early.rav > early.out 2>&1
  [1]
  $ grep -c '^Verification Error: A precondition may not hold' early.out
  1

The frozen-field model uses an explicit acquire capability. Multiple private
writes precede publication; acquiring readers see the final value repeatedly.
The publisher retains its own read capability. A receiving reader needs an
acquire, and later writes lack ownership.

  $ raven --shh publication.rav
  Verification successful.
  $ cat publication.rav no_acquire_fail.rav > no_acquire.rav
  $ raven --shh no_acquire.rav > no_acquire.out 2>&1
  [1]
  $ grep -c '^Verification Error: A precondition may not hold' no_acquire.out
  1
  $ cat publication.rav write_after_publish_fail.rav > write_after.rav
  $ raven --shh write_after.rav > write_after.out 2>&1
  [1]
  $ grep -c '^Verification Error: A precondition may not hold' write_after.out
  1
