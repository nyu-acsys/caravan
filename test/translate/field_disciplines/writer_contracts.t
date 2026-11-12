Explicit writer ownership survives procedure contracts, fractional reads,
generic module adapters and manual predicate packing/unpacking.

  $ caravan --shh writer_contracts.ml
  Verification successful.
  $ caravan --shh writer_generic_contracts.ml
  Verification successful.
  $ caravan --shh --emit-rav writer_contracts.ml > writer_contracts.rav
  $ raven --shh writer_contracts.rav
  Verification successful.

An unknown writer cannot authorize a private read. Plain ownership cannot be
strengthened to current-writer ownership without acquired provenance.

  $ caravan --shh writer_foreign_fail.ml > foreign.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' foreign.out
  $ caravan --shh writer_upgrade_fail.ml > upgrade.out 2>&1
  [1]
  $ grep -q 'A postcondition may not hold' upgrade.out

Writer labels require Frozen fields and a Ghost.t value. Global predicates
must receive the writer explicitly, since they have no executing domain.

  $ caravan --shh writer_invalid.ml > invalid.out 2>&1
  [1]
  $ grep -q 'The writer argument is supported only for Frozen fields' invalid.out
  $ caravan --shh writer_type_fail.ml > type.out 2>&1
  [1]
  $ grep -q 'Type Error' type.out
  $ caravan --shh writer_scope_fail.ml > scope.out 2>&1
  [1]
  $ grep -q "Ghost.self requires an executing procedure's context" scope.out
