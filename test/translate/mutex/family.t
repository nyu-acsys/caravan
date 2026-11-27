Protected resources and native condition operations share polymorphic family instances.

  $ caravan --shh family.ml
  Verification successful.
  $ caravan --shh --emit-rav family.ml > family.rav
  $ raven --shh family.rav
  Verification successful.

A two-parameter carrier can permute its resource-family parameters.

  $ caravan --shh family_pair.ml
  Verification successful.
  $ caravan --shh --emit-rav family_pair.ml > family_pair.rav
  $ raven --shh family_pair.rav
  Verification successful.

A manifest carrier constraint must agree with its implementation.

  $ cp family.ml family_mismatch.ml
  $ sed "s/with type 'a t = 'a t/with type 'a t = int t/" family.mlp > family_mismatch.mlp
  $ ! caravan --shh family_mismatch.ml > mismatch.out 2>&1
  $ grep -q 'does not satisfy its manifest constraint' mismatch.out
