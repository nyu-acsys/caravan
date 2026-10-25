Verify the stack and the module client against the same generated interface.

  $ caravan --shh -I ../../saturn/backoff ../../saturn/treiber_stack/treiber_stack.ml
  Verification successful.

  $ caravan --shh module_stack_drain.ml
  Verification successful.

  $ caravan --shh --emit-rav module_stack_drain.ml > emitted.rav
  $ raven --shh --typeonly emitted.rav
  Verification successful.
