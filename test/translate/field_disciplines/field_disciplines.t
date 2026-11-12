Field declarations select visibility mode without a selector facade.

  $ caravan --shh attributed.ml
  Verification successful.
  $ caravan --shh --emit-rav attributed.ml > attributed.rav
  $ grep -q 'visibility_context' attributed.rav
  $ caravan --shh --emit-rav interface_only.ml > interface_only.rav
  $ grep -q 'visibility_context' interface_only.rav

A private field read requires its storage and current-writer evidence.

  $ caravan --shh gated.ml > gated.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' gated.out

A facade cannot assign a discipline, and attributes belong to fields.

  $ caravan --shh unattributed.ml > unattributed.out 2>&1
  [1]
  $ grep -Fq 'requires [@caravan.frozen]; the field is ordinary' unattributed.out
  $ caravan --shh misplaced.ml > misplaced.out 2>&1
  [1]
  $ grep -q 'attribute belongs on a record field' misplaced.out

A defining signature supplies a field discipline. Existing modules keep
their established discipline at ascriptions and functor applications.

  $ caravan --shh ascription.ml
  Verification successful.
  $ caravan --shh functor_mismatch.ml > functor.out 2>&1
  [1]
  $ grep -q 'requires ordinary access, but the actual field uses frozen access' functor.out
  $ caravan --shh ascription_mismatch.ml > ascription.out 2>&1
  [1]
  $ grep -q 'requires frozen access, but the actual field uses ordinary access' ascription.out
  $ caravan --shh -I imports import_mismatch.ml > import.out 2>&1
  [1]
  $ grep -q 'requires ordinary access, but the actual field uses relaxed access' import.out

A dependent signature preserves field requirements even before application.
Partial application and a manifest result alias preserve the origin's discipline.

  $ caravan --shh symbolic_mismatch.ml > symbolic.out 2>&1
  [1]
  $ grep -q 'requires relaxed access, but the actual field uses frozen access' symbolic.out
  $ caravan --shh partial.ml
  Verification successful.
  $ sed '/^type t = Result\.t /s/: int }/: int [@caravan.relaxed] }/' partial.ml > partial_conflict.ml
  $ caravan --shh partial_conflict.ml > partial_conflict.out 2>&1
  [1]
  $ grep -q 'requires relaxed access, but the actual field uses frozen access' partial_conflict.out

The two facade names share a concrete family. Two separate declarations
with the same payload type have distinct nominal tags.

  $ caravan --shh --emit-rav partial.ml > partial.rav
  $ test "$(grep -c '^module FrozenField_.*_Tag_.* : Library.Type' partial.rav)" -eq 1
  $ test "$(grep -c '^module FrozenFacade_' partial.rav)" -eq 2
  $ test "$(awk '/^module FrozenFacade_/ {print $4}' partial.rav | sort -u | wc -l)" -eq 1
  $ raven --shh partial.rav
  Verification successful.
  $ caravan --shh --emit-rav families.ml > families.rav
  $ test "$(grep -c '^module FrozenField_.*_Tag_.* : Library.Type' families.rav)" -eq 2
  $ raven --shh families.rav
  Verification successful.

Payload dictionaries specialize one nominal field tag. Re-exporting a
specialization shares its existing instance.

  $ caravan --shh --emit-rav generic_families.ml > generic_families.rav
  $ test "$(grep -c '^module FrozenField_.*_Tag_.* : Library.Type' generic_families.rav)" -eq 1
  $ grep -q '^module FrozenField_.*_Family_.*\[V: Ocaml_Value_' generic_families.rav
  $ test "$(grep -c '^  FrozenField_.*_Family_.*\[' generic_families.rav)" -eq 2
  $ test "$(grep -c '^module FrozenFacade_' generic_families.rav)" -eq 3
  $ test "$(awk '/^module FrozenFacade_Integer/ {print $4}' generic_families.rav | sort -u | wc -l)" -eq 1
  $ test "$(awk '/^module FrozenFacade_/ {print $4}' generic_families.rav | sort -u | wc -l)" -eq 2
  $ raven --shh generic_families.rav
  Verification successful.

A Frozen field defined by a functor takes its nominal tag from the result
layout. Repeated applicative applications share it. Unit applications each
get their own tag, and payload specialization does not allocate a new tag.

  $ caravan --shh --emit-rav functor_families.ml > functor_families.rav
  $ test "$(grep -c '^module FrozenField_.*_Tag_.* : Library.Type' functor_families.rav)" -eq 0
  $ test "$(grep -c '^module FrozenFacade_' functor_families.rav)" -eq 5
  $ test "$(awk '/^module FrozenFacade_(Left|Right)_int/ {print $4}' functor_families.rav | sort -u | wc -l)" -eq 1
  $ test "$(awk '/^module FrozenFacade_/ {print $4}' functor_families.rav | sort -u | wc -l)" -eq 4
  $ test "$(grep -c '\.Frozen\[Layout_.*\.FrozenTag_' functor_families.rav)" -eq 4
  $ test "$(sed -n 's/.*\.Frozen\[\(Layout_[^.]*\.FrozenTag_[^,]*\),.*/\1/p' functor_families.rav | sort -u | wc -l)" -eq 3
  $ raven --shh functor_families.rav
  Verification successful.

A defining result signature can supply the discipline for a functor's
fresh field declaration.

  $ caravan --shh --emit-rav projected_family.ml > projected_family.rav
  $ test "$(grep -c '^module FrozenField_.*_Tag_.* : Library.Type' projected_family.rav)" -eq 0
  $ test "$(grep -c '\.Frozen\[Layout_.*\.FrozenTag_' projected_family.rav)" -eq 1
  $ raven --shh projected_family.rav
  Verification successful.

A payload type supplied by a functor argument uses the existing concrete
value dictionary.

  $ caravan --shh --emit-rav dependent_family.ml > dependent_family.rav
  $ grep -q '\.Frozen\[Layout_.*\.FrozenTag_.*, Ocaml_IntValue_' dependent_family.rav
  $ raven --shh dependent_family.rav
  Verification successful.

Generic interfaces carry Frozen field tags, including through signature includes.
Adapters reuse existing tags for aliases and forward symbolic tags when functors
compose. Ownership transfers through both routes, while a different declaration
has separate ownership.

  $ caravan --shh --emit-rav parameter_families.ml > parameter_families.rav
  $ grep -q '^interface Argument_Use_X' parameter_families.rav
  $ grep -q 'Generic_Forward_X.Parameter.FrozenTag_' parameter_families.rav
  $ test "$(grep -c '^module FrozenField_.*_Tag_.* : Library.Type' parameter_families.rav)" -eq 2
  $ awk '/^module Applied_.* : Generic_Forward_X/ {print "module Forwarded_worker: " $2 " = " $2} /^module Applied_.*[.]Generic_Both_Y/ {print "module Second_worker: " $2 " = " $2}' parameter_families.rav > parameter_workers.rav.inc
  $ cat parameter_families.rav parameter_workers.rav.inc parameter_aliases.rav.inc > parameter_aliases.rav
  $ raven --shh parameter_aliases.rav
  Verification successful.
  $ sed 's/ensures ThroughAlias.ownership/ensures ThroughOther.ownership/' parameter_aliases.rav > parameter_distinct_fail.rav
  $ raven --shh parameter_distinct_fail.rav > parameter_distinct.out 2>&1
  [1]
  $ grep -q 'A postcondition may not hold' parameter_distinct.out

The obsolete spelling is rejected rather than silently selecting ordinary access.

  $ caravan --shh obsolete.ml > obsolete.out 2>&1
  [1]
  $ grep -Fq 'has been renamed to [@caravan.relaxed]' obsolete.out
  $ caravan --shh obsolete_misplaced.ml > obsolete_misplaced.out 2>&1
  [1]
  $ grep -Fq 'has been renamed to [@caravan.relaxed]' obsolete_misplaced.out
