A nested static helper remains usable within sealed parents.

  $ caravan --shh zero_nested_sealed.ml
  Verification successful.
  $ caravan --shh --emit-rav zero_nested_sealed.ml > zero_nested_sealed.rav
  $ raven --shh zero_nested_sealed.rav
  Verification successful.

The inner signature hides the helper in source and proof code.

  $ cp zero_nested_sealed.ml zero_nested_sealed_hidden_source.ml
  $ chmod u+w zero_nested_sealed_hidden_source.ml
  $ printf '\nlet leak = World.Inner.Helper.identity 0\n' >> zero_nested_sealed_hidden_source.ml
  $ ! caravan --shh zero_nested_sealed_hidden_source.ml > zero_nested_sealed_hidden_source.out 2>&1
  $ grep -q 'Unbound module World.Inner' zero_nested_sealed_hidden_source.out

  $ cp zero_nested_sealed.ml zero_nested_sealed_hidden_proof.ml
  $ cat zero_nested_sealed.proof > zero_nested_sealed_hidden_proof.proof
  $ printf '\nlemma leak (value : World.Inner.Helper.model) = ()\n' >> zero_nested_sealed_hidden_proof.proof
  $ ! caravan --shh zero_nested_sealed_hidden_proof.ml > zero_nested_sealed_hidden_proof.out 2>&1
  $ grep -q 'Unbound module World.Inner' zero_nested_sealed_hidden_proof.out
