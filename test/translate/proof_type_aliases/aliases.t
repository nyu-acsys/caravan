Proof aliases are transparent in logical functions and inferred predicate arguments.

  $ caravan --shh aliases.ml
  Verification successful.
  $ caravan --shh --emit-rav aliases.ml > aliases.rav
  $ raven --shh aliases.rav
  Verification successful.

An explicit manifest constraint exposes the public carrier equality.

  $ caravan --shh manifest.ml
  Verification successful.
  $ caravan --shh --emit-rav manifest.ml > manifest.rav
  $ raven --shh manifest.rav
  Verification successful.

Reference aliases preserve the restriction on structural equality.

  $ caravan --shh --emit-rav reference_equality.ml > equality.out 2>&1
  [1]
  $ grep -q 'Structural equality on references is unsupported' equality.out

An ordinary colon ascription keeps its carrier opaque.

  $ caravan --shh --emit-rav opaque.ml > opaque.out 2>&1
  [1]
  $ grep -q 'int ref but an expression was expected of type t' opaque.out

The implementation must satisfy its declared manifest equality and spatial member kind.

  $ caravan --shh --emit-rav wrong_manifest.ml > manifest.out 2>&1
  [1]
  $ grep -q 'does not satisfy its manifest constraint' manifest.out
  $ caravan --shh --emit-rav wrong_kind.ml > kind.out 2>&1
  [1]
  $ grep -q 'member resource must be a predicate' kind.out

Unsupported constraint members and incompatible carrier definitions are diagnosed.

  $ caravan --shh --emit-rav wrong_member.ml > member.out 2>&1
  [1]
  $ grep -q 'supports a constraint on type t only' member.out
  $ caravan --shh --emit-rav parameterized_constraint.ml > parameterized.out 2>&1
  [1]
  $ grep -q 'does not satisfy its manifest constraint' parameterized.out
