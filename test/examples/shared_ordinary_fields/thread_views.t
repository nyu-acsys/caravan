The earlier unindexed capability can be copied out of an invariant around an
unrelated atomic read. Its successful proof exposes why it cannot represent
source-thread visibility.

  $ cat publication.rav unindexed_transfer.rav > unindexed.rav
  $ raven --shh unindexed.rav
  Verification successful.

Exclusive contexts carry each executing thread's view. Matching acquires merge
the publication's release view; a second release can propagate it transitively.
Synchronized fork inherits visibility, and join consumes the child's context.
An already-visible reader may still use an unrelated shared invariant.

  $ cat thread_views.rav thread_mailbox.rav thread_clients.rav > threaded.rav
  $ raven --shh threaded.rav
  Verification successful.

Copying a writer's snapshot out of an invariant does not change the executing
thread's view. Acquiring an independent channel does not provide the missing cut.

  $ cat threaded.rav thread_invariant_transfer_fail.rav > invariant_transfer.rav
  $ raven --shh invariant_transfer.rav > invariant_transfer.out 2>&1
  [1]
  $ grep -c '^Verification Error: A precondition may not hold' invariant_transfer.out
  1
  $ cat threaded.rav thread_wrong_acquire_fail.rav > wrong_acquire.rav
  $ raven --shh wrong_acquire.rav > wrong_acquire.out 2>&1
  [1]
  $ grep -c '^Verification Error: A precondition may not hold' wrong_acquire.out
  1

Neither persistent snapshots nor exclusive contexts can be retargeted to the
executing thread, and the exclusive context itself cannot be duplicated.

  $ cat threaded.rav thread_retarget_fail.rav > retarget.rav
  $ raven --shh retarget.rav > retarget.out 2>&1
  [1]
  $ grep -c '^Verification Error: A postcondition may not hold' retarget.out
  1
  $ cat threaded.rav thread_foreign_context_fail.rav > foreign.rav
  $ raven --shh foreign.rav > foreign.out 2>&1
  [1]
  $ grep -c '^Verification Error: A precondition may not hold' foreign.out
  1
  $ cat threaded.rav thread_duplicate_context_fail.rav > duplicate.rav
  $ raven --shh duplicate.rav > duplicate.out 2>&1
  [1]
  $ grep -c '^Verification Error: A postcondition may not hold' duplicate.out
  1

A receiver cannot invent a stronger release view, reuse a joined child's context,
or invoke the hidden context-advance lemma without a synchronization operation.

  $ cat threaded.rav thread_forged_release_fail.rav > release.rav
  $ raven --shh release.rav > release.out 2>&1
  [1]
  $ grep -c '^Verification Error: A precondition may not hold' release.out
  1
  $ cat threaded.rav thread_after_join_fail.rav > joined.rav
  $ raven --shh joined.rav > joined.out 2>&1
  [1]
  $ grep -c '^Verification Error: A precondition may not hold' joined.out
  1
  $ cat threaded.rav thread_hidden_advance_fail.rav > advance.rav
  $ raven --shh advance.rav > advance.out 2>&1
  [1]
  $ grep -c '^Error: advance is not accessible here:' advance.out
  1
