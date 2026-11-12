Constructor-set indices share a carrier while preserving source value domains.
Polymorphic producers retain the required constructor tag at their call sites,
including indexed types without runtime parameters.

  $ caravan --shh rows.ml
  Verification successful.

Mutable inline records own their actual constructor block. Unboxed Link wrappers
preserve its identity through allocations, updates, and CAS. A companion proof file
uses row-index syntax in a reusable ownership predicate.

  $ caravan --shh inline.ml
  Verification successful.
  $ caravan --shh --emit-rav inline.ml > inline.rav
  $ raven --shh inline.rav
  Verification successful.

The same representation works inside generic modules.

  $ caravan --shh modules.ml
  Verification successful.

Inline record parameters follow the compiler layout, including phantom parent
parameters and distinct fields with the same label in different constructors.

  $ caravan --shh phantom.ml
  Verification successful.

A constructor-set index does not supply ownership of its payload.

  $ caravan --shh missing_ownership.ml 2>&1 | grep -c 'Verification Error:'
  1

Ordinary boxed constructors keep conservative physical equality.

  $ caravan --shh boxed_identity.ml 2>&1 | grep -c 'Verification Error:'
  1

Runtime existential payloads and correlated abstract row indices are rejected.

  $ caravan --shh existential.ml 2>&1 | grep -c 'Unsupported Error:'
  1
  $ caravan --shh correlated.ml 2>&1 | grep -c 'Unsupported Error:'
  1
  $ caravan --shh abstract_index.ml 2>&1 | grep -c 'Unsupported Error:'
  1

A refutable constructor parameter needs a matching argument, even when its body
is pure.

  $ caravan --shh parameter_fail.ml 2>&1 | grep -c 'Verification Error:'
  1
