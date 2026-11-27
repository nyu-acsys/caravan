Physical helper calls provide one checked runtime access while an invariant is open.

  $ caravan --shh helpers.ml
  Verification successful.
  $ caravan --shh --emit-rav helpers.ml > helpers.rav
  $ raven --shh helpers.rav
  Verification successful.
  $ caravan --shh shared_fields.ml
  Verification successful.
  $ caravan --shh default_pure.ml
  Verification successful.

Imported and generic module contracts retain their physical atomicity.

  $ caravan --shh -I imports imported.ml
  Verification successful.
  $ caravan --shh generic.ml
  Verification successful.

The physical guarantee cannot be supplied by an ordinary module contract.

  $ caravan --shh weakened.ml > weakened.out 2>&1
  [1]
  $ grep -q 'physically atomic implementation' weakened.out

An attribute cannot turn multiple accesses or an ordinary mutable read into one step.

  $ caravan --shh multiple.ml > multiple.out 2>&1
  [1]
  $ grep -q 'physically atomic' multiple.out
  $ caravan --shh ordinary.ml > ordinary.out 2>&1
  [1]
  $ grep -q 'physically atomic' ordinary.out
  $ caravan --shh default_effect.ml > default_effect.out 2>&1
  [1]
  $ grep -q 'at most one modeled atomic effect' default_effect.out

Physical atomicity is distinct from pure and logically atomic contracts.

  $ caravan --shh conflicting.ml > conflicting.out 2>&1
  [1]
  $ grep -q 'cannot be pure or logically atomic' conflicting.out
  $ caravan --shh pure.ml > pure.out 2>&1
  [1]
  $ grep -q 'cannot be pure or logically atomic' pure.out
