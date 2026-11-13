Relaxed fields expose authoritative journals and persistent observations. Reads
may return any recorded value; they do not promise the current value or acquire
visibility. Source allocation includes the initial write.

  $ caravan --shh generic.ml
  Verification successful.
  $ caravan --shh mixed.ml
  Verification successful.

Existing ghost scopes can snapshot journals, duplicate observations, and reconcile
them with authority. User predicates can maintain properties of all entries
without a separate certificate protocol.

  $ caravan --shh --emit-rav journal.ml > journal.rav
  $ raven --shh journal.rav
  Verification successful.

Imported concrete record declarations preserve their field discipline.

  $ caravan --shh -I imports imported_fail.ml
  Verification successful.
