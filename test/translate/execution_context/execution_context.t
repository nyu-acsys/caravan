Registering unused shared fields enables one execution context across ordinary
calls, exceptional outcomes and generic functor calls, without accessing the fields.

  $ caravan --shh context.ml
  Verification successful.
  $ caravan --shh --emit-rav context.ml > context.rav
  $ awk -f owner.awk context.rav
  $ grep -q 'caravan_execution_entry_held\|execution_token' context.rav
  [1]
  $ raven --shh context.rav
  Verification successful.

Explicit Mutex outcomes and loop invariants retain the visibility authority.

  $ caravan --shh combined.ml
  Verification successful.

A private Frozen read requires its storage and current-writer evidence.

  $ caravan --shh read.ml > read.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' read.out

Atomic loads and Domain tasks carry metadata; native Mutex operations require a facade.

  $ caravan --shh mutex.ml > mutex.out 2>&1
  [1]
  $ grep -q 'Native Mutex access requires a Ghost.Mutex facade' mutex.out
  $ caravan --shh atomic.ml
  Verification successful.
  $ caravan --shh domain.ml
  Verification successful.
