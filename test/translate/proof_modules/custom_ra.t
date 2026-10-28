User-defined resource algebras use ordinary proof modules and Raven checks their laws.

  $ caravan --shh custom_ra.ml
  Verification successful.
  $ caravan --shh --emit-rav custom_ra.ml > custom_ra.rav
  $ raven --shh custom_ra.rav
  Verification successful.

A noncommutative composition fails the inherited algebra law.

  $ ! caravan --shh custom_ra_bad_law.ml > bad_law.out 2>&1
  $ grep -F 'Verification Error:' bad_law.out | head -1
  Verification Error: A postcondition may not hold at this return point.
  $ grep -q 'compCommute' bad_law.out
  $ ! grep -F 'Internal Error:' bad_law.out

The interface seals constructors and private helpers.

  $ cp custom_ra.ml custom_ra_private.ml
  $ ! caravan --shh custom_ra_private.ml > private.out 2>&1
  $ grep -F 'Type Error:' private.out
  Type Error: Unbound constructor Bit.Empty.

Required interface operations cannot be omitted.

  $ cp custom_ra.ml custom_ra_missing.ml
  $ ! caravan --shh custom_ra_missing.ml > missing.out 2>&1
  $ grep -F 'Type Error:' missing.out
  Type Error: The proof-defined resource algebra is missing comp.
