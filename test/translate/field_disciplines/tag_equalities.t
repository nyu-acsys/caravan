The probe is checked inside the generic worker, using only its formal
parameter contracts. A dependent record equation makes the two Frozen
ownership predicates interchangeable.

  $ inject () { awk -v proof_file="$2" '/^[[:space:]]*proc method_id\(/ {while ((getline proof < proof_file) > 0) print proof; close(proof_file)} {print}' "$1"; }
  $ caravan --shh --emit-rav dependent_tags.ml > dependent_tags.rav
  $ inject dependent_tags.rav dependent_tags.rav.inc > dependent_probe.rav
  $ grep -q '^lemma generic_ownership_equality' dependent_probe.rav
  $ raven --shh dependent_probe.rav
  Verification successful.

Removing the type equation leaves independent formal families, even when
both actual arguments happen to name the same module.

  $ sed 's/type t = A.t =/type t =/' dependent_tags.ml > independent_tags.ml
  $ caravan --shh --emit-rav independent_tags.ml > independent_tags.rav
  $ inject independent_tags.rav dependent_tags.rav.inc > independent_probe.rav
  $ raven --shh independent_probe.rav > independent.out 2>&1
  [1]
  $ grep -q 'A postcondition may not hold' independent.out

The same field equality holds for polymorphic record parameters.

  $ sed -e "s/type t = A.t =/type 'a t = 'a A.t =/" -e "s/type t = {/type 'a t = {/" -e "s/counter : int/counter : 'a/" dependent_tags.ml > polymorphic_tags.ml
  $ caravan --shh --emit-rav polymorphic_tags.ml > polymorphic_tags.rav
  $ inject polymorphic_tags.rav dependent_tags.rav.inc > polymorphic_probe.rav
  $ raven --shh polymorphic_probe.rav
  Verification successful.

A trailing unit parameter keeps the dependent equality in the captured
parameters.

  $ sed -e 's/end) =/end) () =/' -e 's/Partial (Actual)/Partial (Actual) ()/' -e 's/Other_partial (Fresh_actual)/Other_partial (Fresh_actual) ()/' dependent_tags.ml > unit_tags.ml
  $ caravan --shh --emit-rav unit_tags.ml > unit_tags.rav
  $ sed 's/Parameter\.FrozenTag/Parameter_1.FrozenTag/' dependent_tags.rav.inc > unit_probe.rav.inc
  $ inject unit_tags.rav unit_probe.rav.inc > unit_probe.rav
  $ raven --shh unit_probe.rav
  Verification successful.

Aliases within one signature share their abstract field tag.

  $ caravan --shh --emit-rav alias_tags.ml > alias_tags.rav
  $ sed 's/Parameter\.FrozenTag_2_1_t7_counter_1/Parameter.FrozenTag_2_1_u7_counter_1/; s/Parameter_0/Parameter/' dependent_tags.rav.inc > alias_probe.rav.inc
  $ inject alias_tags.rav alias_probe.rav.inc > alias_probe.rav
  $ raven --shh alias_probe.rav
  Verification successful.

An equation with a concrete record preserves its already established family.

  $ caravan --shh --emit-rav fixed_tags.ml > fixed_tags.rav
  $ sed 's/Parameter_0.FrozenTag_2_1_t7_counter_1/FrozenField_Known_T_counter_Tag_1/' dependent_tags.rav.inc > fixed_probe.rav.inc
  $ inject fixed_tags.rav fixed_probe.rav.inc > fixed_probe.rav
  $ raven --shh fixed_probe.rav
  Verification successful.
