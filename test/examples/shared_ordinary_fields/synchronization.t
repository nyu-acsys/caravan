One execution context spans integer and Boolean field families. A real Raven
spawn transfers the child's authority into its worker; a one-shot completion
handshake returns it only to join. Mutable atomic writes retain earlier cuts.

  $ cat thread_views.rav thread_spawn.rav thread_atomics.rav > synchronization.rav
  $ raven --shh synchronization.rav
  Verification successful.

A handle cannot be joined twice. Holding a handle without joining does not grant
the parent visibility of the child's publications.

  $ cat synchronization.rav thread_join_twice_fail.rav > twice.rav
  $ raven --shh twice.rav > twice.out 2>&1
  [1]
  $ grep -c '^Verification Error: A precondition may not hold' twice.out
  1
  $ cat synchronization.rav thread_before_join_fail.rav > early.rav
  $ raven --shh early.rav > early.out 2>&1
  [1]
  $ grep -c '^Verification Error: A precondition may not hold' early.out
  1

Replacing accumulated metadata with the overwriter's old view loses the original
publication cut and prevents restoring the atomic-location invariant.

  $ sed 's/ThreadContext.publish(executing, payload, view ++ release ++ {previous})/ThreadContext.publish(executing, payload, view)/' thread_atomics.rav > forget.rav
  $ cat thread_views.rav forget.rav > forgotten.rav
  $ raven --shh forgotten.rav > forgotten.out 2>&1
  [1]
  $ grep -c '^Verification Error:' forgotten.out
  1
