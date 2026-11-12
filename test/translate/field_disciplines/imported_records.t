Concrete imported records share the native representation and field protocols
used by local declarations. Type and module aliases preserve field identity.

  $ caravan --shh -I imports imported_records.ml
  Verification successful.
  $ caravan --shh -I imports --emit-rav imported_records.ml > imported_records.rav
  $ raven --shh imported_records.rav
  Verification successful.

Concrete variants retain their separate unsupported boundary.

  $ caravan --shh -I imports_variant imported_variant_fail.ml > variant.out 2>&1
  [1]
  $ grep -q 'A library type other than an abstract type, alias, or record' variant.out
