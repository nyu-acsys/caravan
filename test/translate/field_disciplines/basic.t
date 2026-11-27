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
