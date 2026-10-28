Scoped proof resources work through structural ascriptions and aliases.

  $ caravan --shh counter.ml
  Verification successful.
  $ caravan --shh siblings.ml
  Verification successful.
  $ caravan --shh nested.ml
  Verification successful.

Every resource exposed by a module signature needs a matching proof definition.

  $ cp counter.ml resource_missing_case.ml
  $ cp counter_missing.proof resource_missing_case.proof
  $ caravan --shh resource_missing_case.ml > resource_missing_case.out 2>&1; status=$?; test "$status" -eq 1 && grep -F 'The module resource zero has no proof definition' resource_missing_case.out
  Type Error: The module resource zero has no proof definition.

The definition must agree with the signature's resource kind and source type.

  $ cp counter.ml resource_kind_case.ml
  $ cp counter_kind.proof resource_kind_case.proof
  $ caravan --shh resource_kind_case.ml > resource_kind_case.out 2>&1; status=$?; test "$status" -eq 1 && grep -F 'The module resource has a different predicate or invariant kind' resource_kind_case.out
  Type Error: The module resource has a different predicate or invariant kind.

  $ cp counter.ml resource_type_case.ml
  $ cp counter_type.proof resource_type_case.proof
  $ caravan --shh resource_type_case.ml > resource_type_case.out 2>&1; status=$?; test "$status" -eq 1 && grep -F 'The module resource has different parameter types' resource_type_case.out
  Type Error: The module resource has different parameter types.

Implicit resource parameter modes must agree too.

  $ caravan --shh resource_modes.ml > resource_modes.out 2>&1; status=$?; test "$status" -eq 1 && grep -F 'The module resource has different implicit parameter modes' resource_modes.out
  Type Error: The module resource has different implicit parameter modes.

The emitted module proof also verifies through Raven's source parser.

  $ caravan --shh --emit-rav counter.ml > counter.rav
  $ raven --shh counter.rav
  Verification successful.
