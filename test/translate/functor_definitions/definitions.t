Unapplied source declarations verify their bodies.

  $ caravan --shh formal.ml
  Verification successful.

An unapplied named functor checks assertions, just like an applied functor.

  $ caravan --shh named_fail.ml > named.output 2>&1
  [1]
  $ grep -q 'Verification Error:' named.output
  $ cat named_fail.ml > applied_fail.ml
  $ echo 'module Actual = struct end' >> applied_fail.ml
  $ echo 'module Instance = Make (Actual)' >> applied_fail.ml
  $ caravan --shh applied_fail.ml > applied.output 2>&1
  [1]
  $ grep -q 'Verification Error:' applied.output

Unit, curried, and nested declarations also check assertions and postconditions.

  $ caravan --shh unit_fail.ml > unit.output 2>&1
  [1]
  $ grep -q 'Verification Error:' unit.output
  $ caravan --shh curried_fail.ml > curried.output 2>&1
  [1]
  $ grep -q 'Verification Error:' curried.output
  $ caravan --shh nested_fail.ml > nested.output 2>&1
  [1]
  $ grep -q 'Verification Error:' nested.output

Companion lemmas are checked without an application.

  $ caravan --shh proof_valid.ml
  Verification successful.
  $ caravan --shh proof_fail.ml > proof.output 2>&1
  [1]
  $ grep -q 'Verification Error:' proof.output

Nested declarations retain outer abstract parameters and their operation contracts.

  $ caravan --shh captured.ml
  Verification successful.
  $ caravan --shh captured_fail.ml > captured.output 2>&1
  [1]
  $ grep -q 'Verification Error:' captured.output

Aliases of formal parameters retain the same abstract operation view.

  $ caravan --shh formal_alias.ml
  Verification successful.
  $ caravan --shh formal_alias_fail.ml > alias.output 2>&1
  [1]
  $ grep -q 'Verification Error:' alias.output

A resource-only parameter may mention an earlier parameter's abstract type.

  $ caravan --shh resource_only.ml
  Verification successful.

An unapplied declaration verifies its own exceptions and handlers.

  $ caravan --shh exceptions.ml
  Verification successful.
  $ caravan --shh exceptions_alias.ml
  Verification successful.

Proof models and lemmas are checked even when the runtime body has no functions.

  $ caravan --shh type_only.ml
  Verification successful.
  $ caravan --shh type_only_fail.ml > type_only.output 2>&1
  [1]
  $ grep -q 'Verification Error:' type_only.output

Curried applications inside an unapplied body retain their enclosing parameters.

  $ caravan --shh symbolic_curried.ml
  Verification successful.

Declarations outside the shared-body optimization still check their functions.

  $ caravan --shh fallback_fail.ml > fallback.output 2>&1
  [1]
  $ grep -q 'Verification Error:' fallback.output

A stronger concrete argument cannot justify a false generic body contract.

  $ caravan --shh specialized_fail.ml > specialized.output 2>&1
  [1]
  $ grep -q 'Verification Error:' specialized.output
