Native atomic operations preserve ordinary ownership contracts while carrying
cumulative synchronization metadata. Fractional ownership permits loads and
provably failing CAS; writes still require the full location.

  $ caravan --shh operations.ml
  Verification successful.
  $ caravan --shh generic.ml
  Verification successful.
  $ caravan --shh locations.ml
  Verification successful.
  $ caravan --shh --emit-rav operations.ml > operations.rav
  $ raven --shh operations.rav
  Verification successful.

  $ caravan --shh partial_write.ml > partial_write.out 2>&1
  [1]
  $ grep -q 'Verification Error: A precondition may not hold' partial_write.out

Programs without shared-field facades retain their existing atomic encoding.

  $ caravan --shh --emit-rav plain.ml > plain.rav
  $ grep -q 'visibility_context\|visibility_frontier' plain.rav
  [1]

Owner-indexed protected resources use checked release/acquire transfers for locks,
successful try-locks, and condition waits. Frozen facts identify the invariant;
visibility is obtained from the protected resource.

  $ caravan --shh mutex.ml
  Verification successful.
  $ caravan --shh --emit-rav mutex.ml > mutex.rav
  $ raven --shh mutex.rav
  Verification successful.

The same protocol supports protected resources declared inside ordinary module
functors, including resource-local proof helpers.

  $ caravan --shh mutex_generic.ml
  Verification successful.

A resource implementation must prove its transfer law.

  $ cp mutex.ml bad_transfer.ml
  $ sed '/Value.transfer source target cell 0;/d' mutex.proof > bad_transfer.proof
  $ caravan --shh bad_transfer.ml > bad_transfer.out 2>&1
  [1]
  $ grep -q 'Verification Error:' bad_transfer.out
  $ grep -qi 'timeout' bad_transfer.out
  [1]

Polymorphic resource aliases retain their type parameters through compositional
transfer helpers, including reordered helper dictionary parameters.

  $ caravan --shh mutex_polymorphic.ml
  Verification successful.
  $ caravan --shh mutex_pair.ml
  Verification successful.
  $ caravan --shh --emit-rav mutex_pair.ml > mutex_pair.rav
  $ raven --shh mutex_pair.rav
  Verification successful.
