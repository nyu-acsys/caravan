Relaxed fields expose authoritative journals and persistent observations. Reads
may return any recorded value; they do not promise the current value or acquire
visibility. Source allocation includes the initial write.

  $ caravan --shh fields.ml
  Verification successful.
  $ caravan --shh generic.ml
  Verification successful.
  $ caravan --shh mixed.ml
  Verification successful.

Existing ghost scopes can snapshot journals, duplicate observations, and reconcile
them with authority. User predicates can maintain properties of all entries
without a separate certificate protocol.

  $ caravan --shh journal.ml
  Verification successful.
  $ caravan --shh --emit-rav journal.ml > journal.rav
  $ raven --shh journal.rav
  Verification successful.

An observation does not grant authority, and authority does not imply freshness.
These are verification failures, rather than timeouts.

  $ caravan --shh missing_state_fail.ml > missing_state.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' missing_state.out
  $ grep -qi 'timeout' missing_state.out
  [1]
  $ caravan --shh latest_fail.ml > latest.out 2>&1
  [1]
  $ grep -q 'A postcondition may not hold' latest.out
  $ grep -qi 'timeout' latest.out
  [1]

Imported concrete record declarations preserve their field discipline.

  $ caravan --shh -I imports imported_fail.ml
  Verification successful.
