Named rank-one functions share workers across scalar and list instantiations.
Contracts and recursive calls preserve the selected value dictionaries.

  $ caravan --shh functions.ml
  Verification successful.
  $ caravan --shh --emit-rav functions.ml > functions.rav
  $ raven --shh functions.rav
  Verification successful.

Structural equality needs a source-type capability beyond value admissibility.

  $ caravan --shh structural_equality.ml > structural_equality.out 2>&1
  [1]
  $ grep -q 'Unsupported\|Type Error:' structural_equality.out
  $ ! grep -q 'Internal Error:' structural_equality.out

Higher-order parameters remain outside the first-order worker translation.

  $ caravan --shh higher_order.ml > higher_order.out 2>&1
  [1]
  $ grep -q 'Unsupported\|Type Error:' higher_order.out
  $ ! grep -q 'Internal Error:' higher_order.out

Checking a contract cannot specialize a universally quantified source variable.

  $ caravan --shh specializing_spec.ml > specializing_spec.out 2>&1
  [1]
  $ grep -q 'Type Error:' specializing_spec.out
  $ ! grep -q 'Internal Error:' specializing_spec.out

Immediate constants cannot specialize generic operands through equality.

  $ caravan --shh generic_bad_equality.ml > generic_bad_equality.out 2>&1
  [1]
  $ grep -q 'Type Error:' generic_bad_equality.out
  $ ! grep -q 'Internal Error:' generic_bad_equality.out

Polymorphic ordering remains unsupported; generic mutable storage is supported.

  $ caravan --shh ordering.ml > ordering.out 2>&1
  [1]
  $ grep -q 'Ordering on polymorphic values' ordering.out
  $ caravan --shh storage.ml
  Verification successful.

Explicit quantified source annotations are rejected until their binder mapping
is supported. Generic proof obligations still reject false contracts.

  $ caravan --shh explicit_scheme.ml > explicit_scheme.out 2>&1
  [1]
  $ grep -q 'explicitly polymorphic function types' explicit_scheme.out
  $ caravan --shh bad_contract.ml > bad_contract.out 2>&1
  [1]
  $ grep -q 'Verification Error:' bad_contract.out
  $ ! grep -q 'Internal Error:' bad_contract.out
