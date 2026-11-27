Native atomic operations preserve ordinary ownership contracts while carrying
cumulative synchronization metadata. Fractional ownership permits loads and
provably failing CAS; writes still require the full location.

  $ caravan --shh operations.ml
  Verification successful.

  $ caravan --shh partial_write.ml > partial_write.out 2>&1
  [1]
  $ grep -q 'Verification Error: A precondition may not hold' partial_write.out

Owner-indexed protected resources use checked release/acquire transfers for locks,
successful try-locks, and condition waits. Frozen facts identify the invariant;
visibility is obtained from the protected resource.

  $ caravan --shh mutex.ml
  Verification successful.

A resource implementation must prove its transfer law.

  $ cp mutex.ml bad_transfer.ml
  $ sed '/Value.transfer source target cell 0;/d' mutex.mlp > bad_transfer.mlp
  $ caravan --shh bad_transfer.ml > bad_transfer.out 2>&1
  [1]
  $ grep -q 'Verification Error:' bad_transfer.out
  $ grep -qi 'timeout' bad_transfer.out
  [1]
