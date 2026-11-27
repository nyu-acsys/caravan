Native mutex handles retain identity through aliases, records, generic functions,
functors and manual scopes. The unit argument is evaluated before allocation.

  $ caravan --shh create.ml
  Verification successful.
  $ caravan --shh scope.ml
  Verification successful.
  $ caravan --shh --emit-rav create.ml > create.rav
  $ raven --shh create.rav
  Verification successful.
  $ caravan --shh --emit-rav scope.ml > scope.rav
  $ raven --shh scope.rav
  Verification successful.

The raw initialization capability is checked and cannot be duplicated.

  $ cp create.rav duplicate.rav
  $ cat >> duplicate.rav <<'RAV'
  > proc duplicate()
  >   requires true
  >   ensures true
  > {
  >   var mutex := Caravan_Mutex_Raw_1.create();
  >   Caravan_Mutex_Raw_1.fresh_exclusive(mutex);
  > }
  > RAV
  $ raven --shh duplicate.rav > duplicate.out 2>&1
  [1]
  $ grep 'Verification Error:' duplicate.out
  Verification Error: A precondition may not hold for this call.

Support is emitted only when allocation is used.

  $ caravan --shh --emit-rav plain.ml > plain.rav
  $ grep 'Caravan_Mutex_Raw' plain.rav
  [1]

Mutex equality follows the existing reference rules, including through containers.

  $ caravan --shh equality.ml > equality.out 2>&1
  [1]
  $ grep 'Error:' equality.out
  Type Error: Structural equality on values containing references is unsupported.
  $ caravan --shh spec_equality.ml > spec_equality.out 2>&1
  [1]
  $ grep 'Error:' spec_equality.out
  Type Error: Structural equality on references is unsupported; use == or != for reference identity.
  $ caravan --shh container_equality.ml > container_equality.out 2>&1
  [1]
  $ grep 'Error:' container_equality.out
  Type Error: Structural equality on values containing references is unsupported.

Acquisition requires a resource facade, while protect remains unsupported.

  $ caravan --shh lock.ml > lock.out 2>&1
  [1]
  $ grep 'Error:' lock.out
  Type Error: Native Mutex access requires a Ghost.Mutex facade.
  $ caravan --shh unlock.ml > unlock.out 2>&1
  [1]
  $ grep 'Error:' unlock.out
  Type Error: Native Mutex access requires a Ghost.Mutex facade.
  $ caravan --shh try_lock.ml > try_lock.out 2>&1
  [1]
  $ grep 'Error:' try_lock.out
  Type Error: Native Mutex access requires a Ghost.Mutex facade.
  $ caravan --shh protect.ml > protect.out 2>&1
  [1]
  $ grep 'Error:' protect.out
  Unsupported Error: Mutex.protect is not supported yet.
