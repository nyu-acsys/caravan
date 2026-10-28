  $ caravan --shh ra_nested_static.ml
  Verification successful.
  $ caravan --shh --emit-rav ra_nested_static.ml > ra_nested_static.rav
  $ raven --shh ra_nested_static.rav
  Verification successful.

Nested definitions must satisfy the same inherited algebra laws.

  $ ! caravan --shh ra_nested_bad_law.ml > nested_bad_law.out 2>&1
  $ grep -q 'Verification Error:' nested_bad_law.out
  $ grep -q 'compCommute' nested_bad_law.out
  $ ! grep -q 'Internal Error:' nested_bad_law.out
