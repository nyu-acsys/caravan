Verify the monomorphic functor client against the imported abstract Treiber stack contract.

  $ caravan --shh functor_stack_drain.ml
  Verification successful.

  $ caravan --shh --emit-rav functor_stack_drain.ml > emitted.rav
  $ raven --shh --typeonly emitted.rav
  Verification successful.
