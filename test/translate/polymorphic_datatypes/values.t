Parameterized variants and immutable records share canonical carriers and source
value dictionaries across generic workers and concrete clients. Recursive values
may contain lists of themselves; phantom and nullary constructors retain context.

  $ caravan --shh values.ml
  Verification successful.
  $ caravan --shh --emit-rav values.ml > values.rav
  $ raven --shh values.rav
  Verification successful.

Generic result equality remains a checked obligation.

  $ caravan --shh bad_contract.ml > bad_contract.out 2>&1
  [1]
  $ grep -q 'Verification Error:' bad_contract.out
  $ ! grep -q 'Internal Error:' bad_contract.out

Pure specification calls do not grant source-value bounds for invalid payloads.

  $ caravan --shh bad_admissibility.ml > bad_admissibility.out 2>&1
  [1]
  $ grep -q 'Verification Error:' bad_admissibility.out
  $ ! grep -q 'Internal Error:' bad_admissibility.out

Unsupported datatype forms are rejected before verification.

  $ caravan --shh gadt.ml > gadt.out 2>&1
  [1]
  $ grep -q 'A GADT beyond constant witnesses' gadt.out
  $ caravan --shh nonregular.ml > nonregular.out 2>&1
  [1]
  $ grep -q 'A nonregular recursive datatype' nonregular.out
  $ caravan --shh mutable.ml > mutable.out 2>&1
  [1]
  $ grep -q 'A mutable record with type parameters' mutable.out
