  $ caravan --shh generic_methods.ml
  Verification successful.

  $ caravan --shh --emit-rav generic_methods.ml > methods.rav
  $ raven --shh --fingerprints methods.rav > methods.fingerprints
  $ grep -c '^[0-9a-f]\{32\} ' methods.fingerprints
  7
  $ grep -c ' Generic_.*\.method_' methods.fingerprints
  3

  $ caravan --shh --emit-rav ordinary.ml > ordinary.rav
  $ raven --shh --fingerprints ordinary.rav > ordinary.fingerprints
  $ grep -c '^[0-9a-f]\{32\} ' ordinary.fingerprints
  5

  $ caravan --shh --emit-rav atomic.ml > atomic.rav
  $ raven --shh --fingerprints atomic.rav > atomic.fingerprints
  $ grep -c '^[0-9a-f]\{32\} ' atomic.fingerprints
  8

  $ caravan --shh generic_manifest.ml
  Verification successful.

  $ caravan --shh generic_persistent.ml
  Verification successful.

  $ caravan --shh --emit-rav generic_persistent.ml > persistent.rav
  $ raven --shh --fingerprints persistent.rav > persistent.fingerprints
  $ grep -c ' Generic_.*\.method_' persistent.fingerprints
  1
  $ grep -c '^[0-9a-f]\{32\} ' persistent.fingerprints
  5
  $ raven --shh persistent.rav
  Verification successful.

  $ caravan --shh generic_ref.ml
  Verification successful.

  $ caravan --shh --emit-rav generic_ref.ml > ref.rav
  $ sed -n '/^module Generic_.*\[/p' ref.rav
  $ raven --shh --typeonly ref.rav
  Verification successful.

  $ caravan --shh generic_composition.ml
  Verification successful.

  $ caravan --shh --emit-rav generic_composition.ml > composition.rav
  $ raven --shh composition.rav
  Verification successful.

  $ caravan --shh generic_later_pure.ml
  Verification successful.

  $ caravan --shh --emit-rav generic_later_pure.ml > pure.rav
  $ raven --shh pure.rav
  Verification successful.

  $ caravan --shh generic_ref_alias.ml
  Verification successful.

  $ caravan --shh --emit-rav generic_ref_alias.ml > ref_alias.rav
  $ sed -n '/^module Generic_.*\[/p' ref_alias.rav
  $ raven --shh --typeonly ref_alias.rav
  Verification successful.

  $ caravan --shh generic_result_view.ml
  Verification successful.

  $ caravan --shh --emit-rav generic_result_view.ml > result_view.rav
  $ raven --shh result_view.rav
  Verification successful.

  $ caravan --shh generic_layout.ml
  Verification successful.

  $ caravan --shh --emit-rav generic_layout.ml > layout.rav
  $ raven --shh --fingerprints layout.rav > layout.fingerprints
  $ grep -c ' World_.*\.method_' layout.fingerprints
  6
  $ grep -c '^module Layout.*Fresh()' layout.rav
  2

  $ caravan --shh generic_layout_payload.ml
  Verification successful.

  $ caravan --shh --emit-rav generic_layout_payload.ml > payload.rav
  $ raven --shh payload.rav
  Verification successful.

  $ caravan --shh generic_layout_unit.ml
  Verification successful.

  $ caravan --shh --emit-rav generic_layout_unit.ml > unit.rav
  $ grep -c '^module Layout.*Fresh()' unit.rav
  2
  $ raven --shh unit.rav
  Verification successful.

  $ caravan --shh generic_layout_fields.ml
  Verification successful.

  $ caravan --shh --emit-rav generic_layout_fields.ml > fields.rav
  $ raven --shh fields.rav
  Verification successful.

  $ caravan --shh generic_shadowed.ml
  Verification successful.

  $ caravan --shh --emit-rav generic_shadowed.ml > shadowed.rav
  $ grep -c '^[[:space:]]*proc method_read(' shadowed.rav
  1
  $ grep -c '^[[:space:]]*proc method_read_1(' shadowed.rav
  1
  $ raven --shh shadowed.rav
  Verification successful.

  $ caravan --shh generic_later_argument_fail.ml
  [Error] File "generic_later_argument_fail.ml", line 15, columns 22-48:
  15 | module Incompatible = Make (Actual.Strong_First)
                             ^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: The module argument's precondition is not provided by this view.
  File "generic_later_argument_fail.ml", line 5, columns 2-21:
  5 |   val read : t -> int
        ^^^^^^^^^^^^^^^^^^^
  Related Location: The requested module operation.
  File "./actual.mli", line 35, columns 2-21:
  35 |   val read : t -> int
         ^^^^^^^^^^^^^^^^^^^
  Related Location: The actual module operation.
  [1]
