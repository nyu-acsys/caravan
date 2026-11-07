An abstract resource algebra in a source signature is checked in one generic worker.

  $ caravan --shh abstract_ra.ml
  Verification successful.
  $ caravan --shh --emit-rav abstract_ra.ml > abstract_ra.rav
  $ raven --shh abstract_ra.rav
  Verification successful.

The worker retains the abstract algebra and ghost fields across both applications.

  $ grep -c '^module Generic_' abstract_ra.rav
  1
  $ grep -c '^module Applied' abstract_ra.rav
  2
  $ grep -c '^  lemma .*identities' abstract_ra.rav
  1
  $ grep -c '^  ghost field .*make_slot' abstract_ra.rav
  1
  $ grep -c 'module R.*ResourceAlgebra' abstract_ra.rav
  1

Every concrete argument must attach the declared algebra.

  $ ! caravan --shh abstract_ra_missing.ml > missing.out 2>&1
  $ grep -q 'Type Error:' missing.out

A proof module with the wrong Raven interface cannot fill the abstract member.

  $ ! caravan --shh abstract_ra_non_ra.ml > non_ra.out 2>&1
  $ grep -q 'Type Error:' non_ra.out

Duplicate abstract members in a source signature are rejected.

  $ ! caravan --shh abstract_ra_duplicate.ml > duplicate.out 2>&1
  $ grep -F 'The module R is already declared' duplicate.out
  Type Error: The module R is already declared.

A source signature alone does not supply its proof member.

  $ ! caravan --shh abstract_ra_signature_only.ml > signature_only.out 2>&1
  $ grep -q 'Type Error:' signature_only.out

Source aliases and named module type aliases preserve the symbolic algebra.

  $ caravan --shh abstract_ra_alias.ml
  Verification successful.
  $ caravan --shh --emit-rav abstract_ra_alias.ml > abstract_ra_alias.rav
  $ raven --shh abstract_ra_alias.rav
  Verification successful.

An imported named signature carries the same abstract resource algebra.

  $ caravan --shh -I abstract_ra_lib abstract_ra_imported.ml
  Verification successful.
  $ caravan --shh -I abstract_ra_lib --emit-rav abstract_ra_imported.ml > abstract_ra_imported.rav
  $ raven --shh abstract_ra_imported.rav
  Verification successful.

Unused declarations still require a known resource algebra interface.

  $ ! caravan --shh abstract_ra_unused_unknown.ml > unused_unknown.out 2>&1
  $ grep -F 'Unknown Raven library interface' unused_unknown.out
  Type Error: Unknown Raven library interface.
  $ ! caravan --shh abstract_ra_unused_non_ra.ml > unused_non_ra.out 2>&1
  $ grep -F 'An abstract proof module must name a ResourceAlgebra interface' unused_non_ra.out
  Type Error: An abstract proof module must name a ResourceAlgebra interface.

Sealed source modules export their declared abstract algebras.

  $ caravan --shh abstract_ra_sealed.ml
  Verification successful.

User-defined algebras satisfy the same generic parameter contract.

  $ caravan --shh abstract_ra_user.ml
  Verification successful.
  $ caravan --shh --emit-rav abstract_ra_user.ml > abstract_ra_user.rav
  $ raven --shh abstract_ra_user.rav
  Verification successful.

Generic updates still require the concrete algebra's permission.

  $ cp abstract_ra.ml abstract_ra_precondition.ml
  $ ! caravan --shh abstract_ra_precondition.ml > precondition.out 2>&1
  $ grep -F 'Verification Error: A precondition may not hold for this call.' precondition.out
  Verification Error: A precondition may not hold for this call.
