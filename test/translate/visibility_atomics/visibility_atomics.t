Native atomic operations preserve ordinary ownership contracts while carrying
cumulative synchronization metadata. Fractional ownership permits loads and
provably failing CAS; writes still require the full location.

  $ caravan --shh generic.ml
  Verification successful.
  $ caravan --shh locations.ml
  Verification successful.
  $ caravan --shh --emit-rav operations.ml > operations.rav
  $ raven --shh operations.rav
  Verification successful.

Programs without shared-field facades retain their existing atomic encoding.

  $ caravan --shh --emit-rav plain.ml > plain.rav
  $ grep -q 'visibility_context\|visibility_frontier' plain.rav
  [1]

Protected-resource programs also verify after Raven serialization.

  $ caravan --shh --emit-rav mutex.ml > mutex.rav
  $ raven --shh mutex.rav
  Verification successful.

The same protocol supports protected resources declared inside ordinary module
functors, including resource-local proof helpers.

  $ caravan --shh mutex_generic.ml
  Verification successful.

Polymorphic resource aliases retain their type parameters through compositional
transfer helpers, including reordered helper dictionary parameters.

  $ caravan --shh mutex_polymorphic.ml
  Verification successful.
  $ caravan --shh mutex_pair.ml
  Verification successful.
  $ caravan --shh --emit-rav mutex_pair.ml > mutex_pair.rav
  $ raven --shh mutex_pair.rav
  Verification successful.
