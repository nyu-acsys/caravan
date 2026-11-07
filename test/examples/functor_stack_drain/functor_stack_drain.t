Verify the monomorphic functor client against the stack's checked interface.

  $ caravan --shh -I ../../saturn/backoff ../../saturn/treiber_stack/treiber_stack.ml
  Verification successful.

  $ caravan --shh functor_stack_drain.ml
  Verification successful.

  $ caravan --shh --emit-rav functor_stack_drain.ml > emitted.rav
  $ raven --shh --typeonly emitted.rav
  Verification successful.
