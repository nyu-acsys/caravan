  $ caravan --shh ra_implicit_attached.ml
  Verification successful.
  $ caravan --shh --emit-rav ra_implicit_attached.ml > ra_implicit_attached.rav
  $ raven --shh ra_implicit_attached.rav
  Verification successful.

Missing or incompatible concrete algebras are still rejected without mirrored blocks.

  $ ! caravan --shh ra_implicit_missing.ml > missing.out 2>&1
  $ grep -q 'Type Error:' missing.out
  $ ! caravan --shh ra_implicit_wrong.ml > wrong.out 2>&1
  $ grep -q 'Type Error:' wrong.out
