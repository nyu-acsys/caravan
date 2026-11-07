Task facades preserve handle resources and keep task bodies checked.

  $ caravan --shh task.ml
  Verification successful.
  $ caravan --shh raises.ml
  Verification successful.
  $ caravan --shh scoped.ml
  Verification successful.

The generated trusted contracts also verify after source emission and parsing.

  $ caravan --shh --emit-rav task.ml > task.rav
  $ raven --shh task.rav
  Verification successful.
  $ caravan --shh --emit-rav raises.ml > raises.rav
  $ raven --shh raises.rav
  Verification successful.
  $ caravan --shh --emit-rav scoped.ml > scoped.rav
  $ raven --shh scoped.rav
  Verification successful.

Aliasing a handle does not duplicate its completion resource.

  $ sed 's/ensures Job.handle result cell/ensures Job.handle result cell \&\& Job.handle domain cell/' task.ml > duplicate.ml
  $ cp task.proof duplicate.proof
  $ caravan --shh duplicate.ml > duplicate.out 2>&1
  [1]
  $ grep 'Verification Error:' duplicate.out
  Verification Error: A postcondition may not hold at this return point.

A task body must establish its declared postcondition even before it is spawned.

  $ sed 's/cell := !cell + 1/cell := !cell + 2/' task.ml > wrong_worker.ml
  $ cp task.proof wrong_worker.proof
  $ caravan --shh wrong_worker.ml > wrong_worker.out 2>&1
  [1]
  $ grep 'Verification Error:' wrong_worker.out
  Verification Error: A postcondition may not hold at this return point.

Task handles retain their source result type despite sharing Raven's Ref carrier.

  $ caravan --shh wrong_result.ml > wrong_result.out 2>&1
  [1]
  $ grep 'Type Error:' wrong_result.out
  Type Error: The value domain has type bool Domain.t

Unsupported task shapes fail at their facade declaration.

  $ caravan --shh ghost.ml > ghost.out 2>&1
  [1]
  $ grep 'Unsupported Error:' ghost.out
  Unsupported Error: A task facade with ghost inputs, ghost results, or history witnesses is not supported yet.
  $ caravan --shh missing_contract.ml > missing_contract.out 2>&1
  [1]
  $ grep 'Type Error:' missing_contract.out
  Type Error: A task facade requires an explicit operation contract.
  $ caravan --shh polymorphic.ml
  Verification successful.

Local modules cannot impersonate the standard library's domain handle type.

  $ caravan --shh shadow_stdlib.ml > shadow_stdlib.out 2>&1
  [1]
  $ grep 'Type Error:' shadow_stdlib.out
  Type Error: A task facade requires the standard-library Domain.t type.

Hidden facades stay inside their module signature boundary.

  $ caravan --shh hidden.ml > hidden.out 2>&1
  [1]
  $ grep 'Unsupported Error:' hidden.out
  Unsupported Error: A call of a function in a contract is not supported yet.

Atomic operation contracts are a separate extension.

  $ caravan --shh atomic.ml > atomic.out 2>&1
  [1]
  $ grep 'Unsupported Error:' atomic.out
  Unsupported Error: A task facade for a logically atomic contract is not supported yet.
