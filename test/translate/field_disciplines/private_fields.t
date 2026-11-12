Frozen fields use checked private storage with allocation-time writer identity.
The same contract is used by source reads/writes, ownership annotations and
proof predicates.

  $ caravan --shh private_fields.ml
  Verification successful.
  $ caravan --shh generic_private_fields.ml
  Verification successful.
  $ caravan --shh --emit-rav private_fields.ml > private_fields.rav
  $ raven --shh private_fields.rav
  Verification successful.
  $ caravan --shh --emit-rav generic_private_fields.ml > generic_private_fields.rav
  $ raven --shh generic_private_fields.rav
  Verification successful.

Ownership received through a contract hides the previous writer. An exact
private read needs the executing owner's last-write evidence. A source rewrite
preserves it for the current writer, including a same-value write.

  $ caravan --shh private_read_fail.ml > read.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' read.out

Writes require full permission. Allocation cannot prove a different value or
duplicate the complete payload/metadata ownership.

  $ caravan --shh private_fraction_fail.ml > fraction.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' fraction.out
  $ caravan --shh private_value_fail.ml > value.out 2>&1
  [1]
  $ grep -q 'A postcondition may not hold' value.out
  $ caravan --shh private_duplicate_fail.ml > duplicate.out 2>&1
  [1]
  $ grep -q 'A postcondition may not hold' duplicate.out

Relaxed ownership requires its dedicated encoding.

  $ caravan --shh private_relaxed_fail.ml > relaxed.out 2>&1
  [1]
  $ grep -q "Relaxed field uses its facade's state predicate" relaxed.out
