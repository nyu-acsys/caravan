Sealed source modules export the declared algebra while retaining private proof members.

  $ caravan --shh ra_exports_sealed.ml
  Verification successful.
  $ caravan --shh --emit-rav ra_exports_sealed.ml > ra_exports_sealed.rav
  $ raven --shh ra_exports_sealed.rav
  Verification successful.

Two sealed modules with the same interface retain distinct resource carriers.

  $ ! caravan --shh ra_exports_sealed_distinct.ml > sealed_distinct.out 2>&1
  $ grep -q 'Type Error:' sealed_distinct.out
  $ ! grep -q 'Internal' sealed_distinct.out
  $ ! caravan --shh ra_exports_source_distinct.ml > source_distinct.out 2>&1
  $ grep -q 'Type Error:' source_distinct.out

A sealed algebra exposes only the ResourceAlgebra interface.

  $ ! caravan --shh ra_exports_sealed_hidden.ml > sealed_hidden.out 2>&1
  $ grep -q 'Type Error:' sealed_hidden.out
  $ ! caravan --shh ra_exports_sealed_helper.ml > sealed_helper.out 2>&1
  $ grep -q 'Type Error:' sealed_helper.out

A sealed source module must implement the declared algebra interface.

  $ ! caravan --shh ra_exports_sealed_missing.ml > sealed_missing.out 2>&1
  $ grep -q 'Type Error:' sealed_missing.out
  $ ! caravan --shh ra_exports_sealed_wrong.ml > sealed_wrong.out 2>&1
  $ grep -q 'Type Error:' sealed_wrong.out

A generic sealed result exports the authority to both application sites.

  $ caravan --shh ra_exports_generic.ml
  Verification successful.
  $ caravan --shh --emit-rav ra_exports_generic.ml > ra_exports_generic.rav
  $ raven --shh ra_exports_generic.rav
  Verification successful.
  $ grep -c '^module Generic_' ra_exports_generic.rav
  1
  $ grep -c '^module Applied' ra_exports_generic.rav
  4
  $ grep -c '^  lemma .*private_identity' ra_exports_generic.rav
  1

Distinct functor arguments produce distinct result algebra carriers.

  $ ! caravan --shh ra_exports_generic_distinct.ml > generic_distinct.out 2>&1
  $ grep -q 'Type Error:' generic_distinct.out

The generic result must implement its declared algebra interface.

  $ ! caravan --shh ra_exports_generic_missing.ml > generic_missing.out 2>&1
  $ grep -q 'Type Error:' generic_missing.out
  $ ! caravan --shh ra_exports_generic_wrong.ml > generic_wrong.out 2>&1
  $ grep -q 'Type Error:' generic_wrong.out

Transparent generic results expose the authority and its resource carrier.

  $ caravan --shh ra_exports_transparent.ml
  Verification successful.
  $ caravan --shh --emit-rav ra_exports_transparent.ml > ra_exports_transparent.rav
  $ raven --shh ra_exports_transparent.rav
  Verification successful.

A transparent native alias preserves its carrier representation.

  $ caravan --shh ra_exports_native.ml
  Verification successful.
  $ ! caravan --shh ra_exports_native_hidden.ml > native_hidden.out 2>&1
  $ grep -q 'Type Error:' native_hidden.out

Nested exports cannot silently change the algebra interface across source seals.

  $ ! caravan --shh ra_exports_chained_weak.ml > chained_weak.out 2>&1
  $ grep -F 'A nested resource algebra export changes interface across source seals' chained_weak.out
  Type Error: A nested resource algebra export changes interface across source seals.
