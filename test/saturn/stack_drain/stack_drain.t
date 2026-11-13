Verify the client against the imported abstract Treiber stack contract.

  $ caravan --shh stack_drain.ml
  Verification successful.

The parallel workers, harness, generic drain and captured loop verify as standalone Raven.

  $ caravan --shh --emit-rav stack_drain.ml > emitted.rav
  $ raven --shh emitted.rav
  Verification successful.

The applied functor emits one shared drain procedure and its captured local helper.

  $ grep -c '^[[:space:]]*proc method_drain(' emitted.rav
  1
  $ grep -c '^[[:space:]]*proc method_loop(' emitted.rav
  1
  $ grep -c '^[[:space:]]*proc method_work(' emitted.rav
  1
  $ grep -c '^[[:space:]]*proc method_test(' emitted.rav
  1

Interface clients drain integer, boolean, and mutable payload stacks and check the parallel harness.

  $ mkdir clients
  $ cp stack_drain.mli treiber_stack.mli clients.ml clients/
  $ caravan --shh clients/clients.ml
  Verification successful.

Clients handle and propagate the exceptions of the interface's raising functions.

  $ caravan --shh raising_call.ml
  Verification successful.
