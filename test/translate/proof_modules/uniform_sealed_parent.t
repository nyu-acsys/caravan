The implementation can use a private unit application under an ascribed parent.

  $ caravan --shh uniform_sealed_parent.ml
  Verification successful.

The public signature hides the application.

  $ cat uniform_sealed_parent.ml > uniform_sealed_parent_hidden.ml
  $ printf '\nlet leak = World.One.read 0\n' >> uniform_sealed_parent_hidden.ml
  $ ! caravan --shh uniform_sealed_parent_hidden.ml > uniform_sealed_parent_hidden.out 2>&1
  $ grep -q 'Unbound module World.One' uniform_sealed_parent_hidden.out

Proof annotations also respect the public signature.

  $ cat uniform_sealed_parent.ml > uniform_sealed_parent_hidden_proof.ml
  $ cat uniform_sealed_parent.proof > uniform_sealed_parent_hidden_proof.proof
  $ printf '\nlemma hidden (token : World.One.Read.token) = ()\n' >> uniform_sealed_parent_hidden_proof.proof
  $ ! caravan --shh uniform_sealed_parent_hidden_proof.ml > uniform_sealed_parent_hidden_proof.out 2>&1
  $ grep -q 'Unbound module World.One' uniform_sealed_parent_hidden_proof.out
