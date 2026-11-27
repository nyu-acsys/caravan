Native operations without a carrier reject ambiguous and missing family instances.

  $ ! caravan --shh family_ambiguous.ml > ambiguous.out 2>&1
  $ grep -q 'The protected resource family instance is ambiguous in this operation' ambiguous.out

  $ ! caravan --shh family_missing.ml > missing.out 2>&1
  $ grep -q "Cannot infer the protected resource family from this operation's carrier types" missing.out
