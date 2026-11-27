Waiting requires ownership of the associated mutex.

  $ sed '/let await mutex condition =/,/let signal condition =/{/  Mutex.lock mutex;/d;}' basic.ml > unlocked.ml
  $ cp basic.mlp unlocked.mlp
  $ caravan --shh unlocked.ml > unlocked.out 2>&1
  [1]
  $ grep -m1 -o 'A precondition may not hold' unlocked.out
  A precondition may not hold

A condition can only be waited on with its associated mutex.

  $ caravan --shh wrong_mutex.ml > wrong_mutex.out 2>&1
  [1]
  $ grep -m1 -o 'A precondition may not hold' wrong_mutex.out
  A precondition may not hold

The condition initialization capability cannot be consumed twice.

  $ cp basic.ml double_initialize.ml
  $ sed 's/Guard.initialize_condition condition mutex;/Guard.initialize_condition condition mutex; Guard.initialize_condition condition mutex;/' basic.mlp > double_initialize.mlp
  $ caravan --shh double_initialize.ml > double_initialize.out 2>&1
  [1]
  $ grep -m1 -o 'A precondition may not hold' double_initialize.out
  A precondition may not hold

An allocated condition is not associated until it is initialized.

  $ cp basic.ml uninitialized.ml
  $ sed '/    Guard.initialize_condition condition mutex;/d' basic.mlp > uninitialized.mlp
  $ caravan --shh uninitialized.ml > uninitialized.out 2>&1
  [1]
  $ grep -m1 -o 'A postcondition may not hold' uninitialized.out
  A postcondition may not hold

Notification grants no protected resource ownership.

  $ caravan --shh signal_no_resource.ml > signal_no_resource.out 2>&1
  [1]
  $ grep -m1 -o 'A postcondition may not hold' signal_no_resource.out
  A postcondition may not hold

Wait returns a refreshed protected state, even when the old value was read.

  $ cp basic.ml stale_value.ml
  $ sed '/  at (Condition.wait condition mutex) (fun invoke ->/,/  at (Mutex.unlock mutex)/s/    unfold Cell.resource cell;/    unfold Cell.resource cell; assert (own cell.contents before);/' basic.mlp > stale_value.mlp
  $ caravan --shh stale_value.ml > stale_value.out 2>&1
  [1]
  $ grep -m1 -o 'This assertion may be violated' stale_value.out
  This assertion may be violated

A wakeup does not prove that a previously true guard is still true.

  $ caravan --shh spurious_guard.ml > spurious_guard.out 2>&1
  [1]
  $ grep -m1 -o 'A postcondition may not hold' spurious_guard.out
  A postcondition may not hold

Condition handles retain their distinct OCaml type and reference identity.

  $ caravan --shh structural.ml > structural.out 2>&1
  [1]
  $ grep -m1 -o 'Structural equality on values containing references is unsupported' structural.out
  Structural equality on values containing references is unsupported
  $ caravan --shh type_confusion.ml > type_confusion.out 2>&1
  [1]
  $ grep -m1 -o 'Logical equality requires operands of the same OCaml type' type_confusion.out
  Logical equality requires operands of the same OCaml type
