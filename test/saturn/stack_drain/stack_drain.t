Verify the implementation and client against the same Treiber interface.

  $ caravan --shh -I ../backoff ../treiber_stack/treiber_stack.ml
  Verification successful.

The client uses only the imported abstract stack contract.

  $ caravan --shh stack_drain.ml
  Verification successful.

Clients handle and propagate the exceptions of the interface's raising functions.

  $ caravan --shh raising_call.ml
  Verification successful.
