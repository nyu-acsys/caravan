A facade installs a checked spatial resource; critical sections preserve the
current execution owner and entry lock set through helpers, loops and exceptions.

  $ caravan --shh initialize.ml
  Verification successful.
  $ caravan --shh critical.ml
  Verification successful.
  $ caravan --shh cleanup.ml
  Verification successful.
  $ caravan --shh trivial.ml
  Verification successful.
  $ caravan --shh --emit-rav critical.ml > critical.rav
  $ raven --shh critical.rav
  Verification successful.
  $ caravan --shh --emit-rav cleanup.ml > cleanup.rav
  $ raven --shh cleanup.rav
  Verification successful.

Recursive acquisition is rejected even with the original held token framed out.

  $ sed 's/let success = Mutex.try_lock mutex in/Mutex.lock mutex; let success = Mutex.try_lock mutex in/' critical.ml > recursive.ml
  $ cp critical.proof recursive.proof
  $ caravan --shh recursive.ml > recursive.out 2>&1
  [1]
  $ grep -q 'Verification Error: A precondition may not hold' recursive.out

The caller must supply availability, rather than merely a persistent association.

  $ cp critical.ml unavailable.ml
  $ sed 's/not (Finset.mem mutex held)/true/g' critical.proof > unavailable.proof
  $ caravan --shh unavailable.ml > unavailable.out 2>&1
  [1]
  $ grep -q 'Verification Error: A precondition may not hold' unavailable.out

Unlock needs the protected resource folded back, and a lock cannot be leaked.

  $ cp critical.ml missing_resource.ml
  $ sed 's/^    fold Cell.resource cell;/    ();/' critical.proof > missing_resource.proof
  $ caravan --shh missing_resource.ml > missing_resource.out 2>&1
  [1]
  $ grep -q 'Verification Error: A precondition may not hold' missing_resource.out
  $ sed 's/Mutex.unlock mutex/if false then Mutex.unlock mutex/g' critical.ml > leaked.ml
  $ cp critical.proof leaked.proof
  $ caravan --shh leaked.ml > leaked.out 2>&1
  [1]
  $ grep -q 'Verification Error: A postcondition may not hold' leaked.out

Context preservation applies on the exceptional exit too.

  $ sed 's/Mutex.unlock mutex;/if not error then Mutex.unlock mutex;/' cleanup.ml > leaked_exception.ml
  $ cp cleanup.proof leaked_exception.proof
  $ caravan --shh leaked_exception.ml > leaked_exception.out 2>&1
  [1]
  $ grep -q 'Verification Error: A postcondition may not hold' leaked_exception.out

A failed try-lock grants no access to the protected cell.

  $ caravan --shh failed_try.ml > failed_try.out 2>&1
  [1]
  $ grep -q 'Verification Error: A precondition may not hold' failed_try.out

Initializing one physical mutex twice cannot duplicate its protocol.

  $ cp initialize.ml twice.ml
  $ sed 's/Guard.initialize mutex cell;/Guard.initialize mutex cell; Guard.initialize mutex cell;/' initialize.proof > twice.proof
  $ caravan --shh twice.ml > twice.out 2>&1
  [1]
  $ grep -q 'Verification Error: A precondition may not hold' twice.out

Domain tasks preserve the caller's execution context.

  $ caravan --shh domain.ml
  Verification successful.

Checked module forwarding preserves the execution context.

  $ caravan --shh checked_module.ml
  Verification successful.

A token acquired by another execution owner cannot release this mutex.

  $ caravan --shh wrong_owner.ml > wrong_owner.out 2>&1
  [1]
  $ grep -q 'Verification Error: A precondition may not hold' wrong_owner.out

Context clauses describe one existing execution context, not extra copies.

  $ cp critical.ml duplicate_context.ml
  $ sed 's/Ghost.Mutex.context self held/Ghost.Mutex.context self held \&\& Ghost.Mutex.context self held/g' critical.proof > duplicate_context.proof
  $ caravan --shh duplicate_context.ml > duplicate_context.out 2>&1
  [1]
  $ grep -q 'at most one mutex context clause' duplicate_context.out
