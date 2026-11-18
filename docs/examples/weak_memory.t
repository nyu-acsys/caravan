The weak-memory tutorial examples are checked with their external proofs.

  $ caravan --shh owned_job.ml
  Verification successful.

  $ caravan --shh frozen_job.ml
  Verification successful.

  $ caravan --shh relaxed_job.ml
  Verification successful.

The parent cannot read storage transferred to the worker before joining it.

  $ sed 's/  Domain.join worker/  let _ = inspect job in Domain.join worker/' owned_job.ml > early_read.ml
  $ cp owned_job.proof early_read.proof
  $ caravan --shh early_read.ml > early_read.out 2>&1
  [1]
  $ grep -q 'Verification Error:' early_read.out
  $ grep -qi 'timeout' early_read.out
  [1]

A frozen read needs its field-specific scope.

  $ cp frozen_job.ml ordinary_read.ml
  $ sed 's/Ghost.frozen_scope/Ghost.scope/g' frozen_job.proof > ordinary_read.proof
  $ caravan --shh ordinary_read.ml > ordinary_read.out 2>&1
  [1]
  $ grep -q 'Verification Error:' ordinary_read.out
  $ grep -qi 'timeout' ordinary_read.out
  [1]

An unrestricted read does not inherit acquired publication guarantees.

  $ sed 's/Ghost.published_scope/Ghost.scope/' relaxed_job.proof > unrestricted.proof
  $ cp relaxed_job.ml unrestricted.ml
  $ caravan --shh unrestricted.ml > unrestricted.out 2>&1
  [1]
  $ grep -q 'Verification Error:' unrestricted.out
  $ grep -qi 'timeout' unrestricted.out
  [1]
