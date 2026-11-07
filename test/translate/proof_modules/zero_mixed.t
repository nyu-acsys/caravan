Static modules share proof resources with aliases and can be captured by functors.

  $ caravan --shh zero_mixed.ml
  Verification successful.
  $ caravan --shh --emit-rav zero_mixed.ml > zero_mixed.rav
  $ raven --shh zero_mixed.rav
  Verification successful.
  $ grep -c '^ghost field proof_static_slot' zero_mixed.rav
  1
  $ grep -c '^pred static_held' zero_mixed.rav
  1

A static alias denotes the same field descriptor, so it cannot initialize it twice.

  $ cp zero_mixed.ml zero_mixed_duplicate_field.ml
  $ cat zero_mixed.proof > zero_mixed_duplicate_field.proof
  $ printf '\nlemma duplicate = let cell = Ghost.alloc [Ghost.init Static.slot 0; Ghost.init Static_alias.slot 0] in ()\n' >> zero_mixed_duplicate_field.proof
  $ ! caravan --shh zero_mixed_duplicate_field.ml > zero_mixed_duplicate_field.out 2>&1
  $ grep -q 'Type Error: A ghost field is initialized more than once.' zero_mixed_duplicate_field.out
  $ ! grep -Eq 'Syntax Error:|Internal Error:' zero_mixed_duplicate_field.out

A fresh unit application has a different predicate resource.

  $ cp zero_mixed.ml zero_mixed_wrong_predicate.ml
  $ cat zero_mixed.proof > zero_mixed_wrong_predicate.proof
  $ printf '\nlemma wrong (cell : Ghost.t) requires (Static.held cell 0) ensures (Fresh.held cell 0) = ()\n' >> zero_mixed_wrong_predicate.proof
  $ ! caravan --shh zero_mixed_wrong_predicate.ml > zero_mixed_wrong_predicate.out 2>&1
  $ grep -Eq 'Verification Error:|Type Error:' zero_mixed_wrong_predicate.out
  $ ! grep -Eq 'Syntax Error:|Internal Error:' zero_mixed_wrong_predicate.out

Its model is distinct from the static model.

  $ cp zero_mixed.ml zero_mixed_wrong_model.ml
  $ cat zero_mixed.proof > zero_mixed_wrong_model.proof
  $ printf '\nlemma wrong_model (value : Static.model) ensures (Fresh.payload value = 0) = ()\n' >> zero_mixed_wrong_model.proof
  $ ! caravan --shh zero_mixed_wrong_model.ml > zero_mixed_wrong_model.out 2>&1
  $ grep -q 'Type Error: The value value has type Static.model' zero_mixed_wrong_model.out
  $ ! grep -Eq 'Syntax Error:|Internal Error:' zero_mixed_wrong_model.out
