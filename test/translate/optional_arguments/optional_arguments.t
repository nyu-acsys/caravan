Optional inputs retain their option carrier. Defaults use ordinary entry code,
including dependent defaults, tuple patterns, pure functions and exact constants.

  $ caravan --shh basic.ml
  Verification successful.
  $ caravan --shh modules.ml
  Verification successful.
  $ caravan --shh -I imports imports.ml
  Verification successful.

Defaults run only when absent, after the precondition. Proof steps can annotate
the default expression, and local helpers capture the selected value.

  $ caravan --shh pattern_order.ml
  Verification successful.
  $ caravan --shh provenance.ml
  Verification successful.
  $ caravan --shh cases.ml
  Verification successful.
  $ caravan --shh effects.ml
  Verification successful.
  $ caravan --shh --emit-rav effects.ml > effects.rav
  $ raven --shh effects.rav
  Verification successful.

Exceptions raised by defaults participate in the ordinary exceptional contract.
A supplied argument bypasses a raising default.

  $ caravan --shh raising.ml
  Verification successful.
  $ caravan --shh undeclared.ml > undeclared.out 2>&1
  [1]
  $ grep -q 'Missing' undeclared.out

Default-only proof exports cannot escape to an unconditional return.

  $ caravan --shh conditional_export.ml > export.out 2>&1
  [1]
  $ grep -q 'does not run on every' export.out

  $ caravan --shh cases_export.ml > cases.out 2>&1
  [1]
  $ grep -q 'does not run on every' cases.out
  $ caravan --shh nested_export.ml > nested.out 2>&1
  [1]
  $ grep -q 'does not run on every' nested.out

A write in a default cannot be hidden by declaring the function pure.

  $ caravan --shh pure_default.ml > pure.out 2>&1
  [1]

Refutable parameter patterns still need a precondition excluding unmatched values.

  $ caravan --shh unsafe_pattern.ml > pattern.out 2>&1
  [1]
  $ grep -c 'Verification Error:' pattern.out
  2
  $ grep -qi timeout pattern.out
  [1]

Partial applications remain unsupported.

  $ caravan --shh partial.ml > partial.out 2>&1
  [1]
  $ grep -q 'Unsupported Error:' partial.out

Body scopes after defaults and entry patterns retain their enclosing function.

  $ caravan --shh body_scopes.ml
  Verification successful.
