Logical atomic updates capture their execution owner, while visibility authority
remains in the ordinary contract. Abort preserves visibility acquired by the
physical atomic operation. Tokens also work in proof lemmas, generic modules,
and combined mutex/visibility mode.

  $ caravan --shh logical.ml
  Verification successful.
  $ caravan --shh logical_acquire.ml
  Verification successful.
  $ caravan --shh logical_combined.ml
  Verification successful.
  $ caravan --shh logical_generic.ml
  Verification successful.
  $ caravan --shh logical_imported.ml
  Verification successful.

Opening and aborting a logical update does not itself acquire visibility.

  $ caravan --shh logical_unseen.ml > logical_unseen.out 2>&1
  [1]
  $ grep -q 'Verification Error: A precondition may not hold' logical_unseen.out

Both captured-token layouts survive Raven printing and parsing.

  $ caravan --shh --emit-rav logical_acquire.ml > logical_acquire.rav
  $ raven --shh logical_acquire.rav
  Verification successful.
  $ caravan --shh --emit-rav logical_combined.ml > logical_combined.rav
  $ raven --shh logical_combined.rav
  Verification successful.
