Frozen facades seal full current-writer ownership and expose a persistent fact.
Selectors cover polymorphic named records, inline records and generic functors.

  $ caravan --shh freeze_fields.ml
  Verification successful.
  $ caravan --shh --emit-rav freeze_fields.ml > freeze_fields.rav
  $ raven --shh freeze_fields.rav
  Verification successful.

Ownership alone cannot authorize a foreign-writer freeze. Freezing also needs
full permission and consumes the private ownership.

  $ caravan --shh freeze_foreign_fail.ml > foreign.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' foreign.out
  $ caravan --shh freeze_partial_fail.ml > partial.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' partial.out
  $ caravan --shh freeze_repeat_fail.ml > repeat.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' repeat.out
  $ caravan --shh freeze_write_fail.ml > write.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' write.out

Frozen facts retain the value and nominal field identity.

  $ caravan --shh freeze_value_fail.ml > value.out 2>&1
  [1]
  $ grep -q 'A postcondition may not hold' value.out
  $ caravan --shh freeze_field_fail.ml > field.out 2>&1
  [1]
  $ grep -q 'A postcondition may not hold' field.out
  $ caravan --shh freeze_constructor_fail.ml > constructor.out 2>&1
  [1]
  $ grep -q 'A postcondition may not hold' constructor.out
