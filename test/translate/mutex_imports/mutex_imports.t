The client preserves its held set through imported contracts at the top level
and inside a nested module.

  $ caravan --shh client.ml
  Verification successful.

A second acquire violates the imported precondition.

  $ caravan --shh --only duplicate_acquire negative.ml > duplicate.out 2>&1
  [1]
  $ grep -q 'Verification Error: A precondition may not hold' duplicate.out

Omitting the release violates the client's postcondition.

  $ caravan --shh --only missing_release negative.ml > missing.out 2>&1
  [1]
  $ grep -q 'Verification Error: A postcondition may not hold' missing.out
