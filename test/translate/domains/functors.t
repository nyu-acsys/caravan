Task facades share their enclosing functor's translation and instance identity.

  $ caravan --shh functor.ml
  Verification successful.
  $ caravan --shh functor_parameters.ml
  Verification successful.
  $ caravan --shh functor_curried.ml
  Verification successful.
  $ caravan --shh functor_hidden.ml
  Verification successful.
  $ caravan --shh functor_raises.ml
  Verification successful.

Emitted functors and their task contracts also verify independently.

  $ caravan --shh --emit-rav functor.ml > functor.rav
  $ raven --shh functor.rav
  Verification successful.
  $ caravan --shh --emit-rav functor_parameters.ml > functor_parameters.rav
  $ raven --shh functor_parameters.rav
  Verification successful.
  $ caravan --shh --emit-rav functor_curried.ml > functor_curried.rav
  $ raven --shh functor_curried.rav
  Verification successful.
  $ caravan --shh --emit-rav functor_hidden.ml > functor_hidden.rav
  $ raven --shh functor_hidden.rav
  Verification successful.
  $ caravan --shh --emit-rav functor_raises.ml > functor_raises.rav
  $ raven --shh functor_raises.rav
  Verification successful.

Generative applications cannot exchange completion claims.

  $ sed 's/First.finish first/Second.finish first/' functor.ml > generative.ml
  $ cp functor.mlp generative.mlp
  $ caravan --shh generative.ml > generative.out 2>&1
  [1]
  $ grep 'Verification Error:' generative.out
  Verification Error: A precondition may not hold for this call.

Distinct named arguments stay distinct even with identical carrier types.

  $ sed 's/Again.finish first 7/Third.finish first 7/' functor_parameters.ml > distinct.ml
  $ cp functor_parameters.mlp distinct.mlp
  $ caravan --shh distinct.ml > distinct.out 2>&1
  [1]
  $ grep 'Verification Error:' distinct.out
  Verification Error: A precondition may not hold for this call.

An unapplied functor's worker body is checked at its declaration.

  $ sed '/module First = Worker ()/,$d; s/let work () = 1/let work () = 2/' functor.ml > unapplied.ml
  $ cp functor.mlp unapplied.mlp
  $ caravan --shh unapplied.ml > unapplied.out 2>&1
  [1]
  $ grep 'Verification Error:' unapplied.out
  Verification Error: A postcondition may not hold at this return point.
