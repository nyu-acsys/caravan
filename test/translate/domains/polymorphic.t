Task instances share the existing dictionary-based polymorphic translation.

  $ caravan --shh polymorphic_runtime.ml
  Verification successful.
  $ caravan --shh polymorphic_raises.ml
  Verification successful.
  $ caravan --shh --emit-rav polymorphic_runtime.ml > polymorphic_runtime.rav
  $ raven --shh polymorphic_runtime.rav
  Verification successful.
  $ caravan --shh --emit-rav polymorphic_raises.ml > polymorphic_raises.rav
  $ raven --shh polymorphic_raises.rav
  Verification successful.

Source handle and capture types must agree before erasure to Ref.

  $ caravan --shh polymorphic_wrong.ml > wrong.out 2>&1
  [1]
  $ grep 'Type Error:' wrong.out
  Type Error: Cannot infer consistent task type parameters from the handle and captured arguments.

Different capture types do not share completion claims even with identical result types.

  $ caravan --shh polymorphic_instance.ml > instance.out 2>&1
  [1]
  $ grep 'Verification Error:' instance.out
  Verification Error: A precondition may not hold for this call.

Polymorphic handles preserve exclusive completion resources.

  $ sed 's/let previous = Domain.join domain in/let ignored = !cell in let previous = Domain.join domain in/' polymorphic_runtime.ml > early.ml
  $ cp polymorphic_runtime.mlp early.mlp
  $ caravan --shh early.ml > early.out 2>&1
  [1]
  $ grep 'Verification Error:' early.out
  Verification Error: A precondition may not hold for this call.
  $ sed 's/let previous = Domain.join domain in/let previous = Domain.join domain in let duplicate = Domain.join domain in/' polymorphic_runtime.ml > twice.ml
  $ cp polymorphic_runtime.mlp twice.mlp
  $ caravan --shh twice.ml > twice.out 2>&1
  [1]
  $ grep 'Verification Error:' twice.out
  Verification Error: A precondition may not hold for this call.
