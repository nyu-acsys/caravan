The inner proof can use its private unit application under a sealed signature.

  $ caravan --shh uniform_nested_sealed_parent.ml
  Verification successful.

The inner public signature hides the application.

  $ cat uniform_nested_sealed_parent.ml > uniform_nested_sealed_parent_hidden.ml
  $ printf '\nlet leak = World.Inner.One.read 0\n' >> uniform_nested_sealed_parent_hidden.ml
  $ ! caravan --shh uniform_nested_sealed_parent_hidden.ml > uniform_nested_sealed_parent_hidden.out 2>&1
  $ grep -q 'Unbound module World.Inner.One' uniform_nested_sealed_parent_hidden.out

Proof annotations also respect the public signature.

  $ cat uniform_nested_sealed_parent.ml > uniform_nested_sealed_parent_hidden_proof.ml
  $ cat uniform_nested_sealed_parent.proof > uniform_nested_sealed_parent_hidden_proof.proof
  $ printf '\nlemma hidden (token : World.Inner.One.Read.token) = ()\n' >> uniform_nested_sealed_parent_hidden_proof.proof
  $ ! caravan --shh uniform_nested_sealed_parent_hidden_proof.ml > uniform_nested_sealed_parent_hidden_proof.out 2>&1
  $ grep -q 'Unbound module World.Inner.One' uniform_nested_sealed_parent_hidden_proof.out
