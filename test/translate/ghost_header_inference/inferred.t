Unnamed native parameters are inferred jointly with ghost header annotations,
without changing generic lemma schemes or losing branch result context.

  $ caravan --shh inferred.ml
  Verification successful.

An owner determines the field and the context of nested polymorphic empty values.

  $ caravan --shh field_context.ml
  Verification successful.

Concrete stored values must still match that owner-derived context.

  $ caravan --shh field_context_fail.ml > field_context_fail.out 2>&1
  [1]
  $ grep -q 'Type Error:' field_context_fail.out
  $ ! grep -q 'Internal Error:' field_context_fail.out
  $ ! grep -q 'Assertion failed' field_context_fail.out

Parameterized mathematical record witnesses retain mathematical list domains.

  $ caravan --shh record_domains.ml
  Verification successful.

Runtime records still require source-admissible field values.

  $ caravan --shh runtime_record_fail.ml > runtime_record_fail.out 2>&1
  [1]
  $ grep -q 'Verification Error:' runtime_record_fail.out
  $ ! grep -q 'timed out' runtime_record_fail.out
  $ ! grep -q 'Internal Error:' runtime_record_fail.out

Scoped proof types retain the lexical type identities of local helper headers.

  $ caravan --shh modules.ml
  Verification successful.
