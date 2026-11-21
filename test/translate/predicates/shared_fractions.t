An invariant can lend part of its fraction to a read that follows its closing.

  $ caravan --shh shared_fractions.ml
  Verification successful.

Returning the whole fraction leaves nothing to read with.

  $ caravan --shh shared_fractions_fail.ml
  [Error] File "shared_fractions_fail.ml", line 3, columns 23-31:
  3 | let read (job : job) = job.work
                             ^^^^^^^^
  Verification Error: A precondition may not hold for this call.
  Related Location: This assertion may not hold
  Related Location: This own predicate may not hold
  [1]
