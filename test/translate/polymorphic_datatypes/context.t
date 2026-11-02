Record literals inherit their element type from the other equality operand.

  $ caravan --shh context.ml
  Verification successful.
  $ caravan --shh --emit-rav context.ml > context.rav
  $ raven --shh context.rav
  Verification successful.

The same context cannot specialize a universally quantified source type.

  $ caravan --shh specializing_context.ml > specializing_context.out 2>&1
  [1]
  $ grep -q 'Type Error:' specializing_context.out
  $ ! grep -q 'Internal Error:' specializing_context.out
