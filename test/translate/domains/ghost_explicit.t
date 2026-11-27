Spawn captures explicit ghost inputs and join exposes the task's ghost results.

  $ caravan --shh ghost_explicit.ml
  Verification successful.
  $ caravan --shh --emit-rav ghost_explicit.ml > ghost_explicit.rav
  $ raven --shh ghost_explicit.rav
  Verification successful.

Polymorphic ghost values retain their types through functor task instances.

  $ caravan --shh ghost_explicit_functor.ml
  Verification successful.
  $ caravan --shh --emit-rav ghost_explicit_functor.ml > ghost_explicit_functor.rav
  $ raven --shh ghost_explicit_functor.rav
  Verification successful.

Raising tasks expose ghost results on normal completion and return ownership on both paths.

  $ caravan --shh ghost_explicit_raises.ml
  Verification successful.
  $ caravan --shh --emit-rav ghost_explicit_raises.ml > ghost_explicit_raises.rav
  $ raven --shh ghost_explicit_raises.rav
  Verification successful.

Spawn cannot expose the task's future ghost result.

  $ caravan --shh ghost_explicit_raises_early.ml > early_ghost.out 2>&1
  [1]
  $ grep -q 'The proof pattern does not match its input type' early_ghost.out

A missing ghost input is rejected at spawn.

  $ caravan --shh ghost_explicit_missing.ml > missing.out 2>&1
  [1]
  $ grep -q 'Caravan cannot tell the ghost argument of this call' missing.out

A spawn scope must pass the declared number of ghost inputs.

  $ caravan --shh ghost_explicit_count.ml > count.out 2>&1
  [1]
  $ grep -q 'This expression has type .* but an expression was expected of type int' count.out
