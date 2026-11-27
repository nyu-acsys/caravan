Proof-defined interface members remain available while helpers stay within the definition.

  $ caravan --shh --emit-rav private_helpers.ml > private_helpers.rav

Private predicates cannot be named outside the public resource interface.

  $ caravan --shh --emit-rav private_predicate.ml > predicate.out 2>&1
  [1]
  $ grep -q 'Unknown proof module member Cell.secret' predicate.out

A resource alias cannot expose a private function or lemma.

  $ caravan --shh --emit-rav private_function.ml > function.out 2>&1
  [1]
  $ grep -q 'Type Error:' function.out
  $ caravan --shh --emit-rav private_type_name_function.ml > type_name.out 2>&1
  [1]
  $ grep -q 'Type Error:' type_name.out
  $ caravan --shh --emit-rav private_lemma.ml > lemma.out 2>&1
  [1]
  $ grep -q 'Unknown lemma Alias.private_helper' lemma.out

A nested runtime Ghost module retains its own context function and list argument.

  $ caravan --shh --emit-rav context_shadow.ml > context_shadow.rav
  $ raven --shh context_shadow.rav
  Verification successful.
