Verify the module client against the imported abstract Treiber stack contract.

  $ caravan --shh module_stack_drain.ml
  Verification successful.

  $ caravan --shh --emit-rav module_stack_drain.ml > emitted.rav
  $ raven --shh --typeonly emitted.rav
  Verification successful.
