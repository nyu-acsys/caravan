Unit, named-parameter, curried and exceptional Domain functors use the same
execution boundary as ordinary procedures.

  $ cp ../domains/functor.ml unit_functor.ml
  $ cat ../domains/functor.mlp unit_resource.mlp > unit_functor.mlp
  $ caravan --shh unit_functor.ml
  Verification successful.
  $ sed '/^module First =/,$d' unit_functor.ml > unit_unapplied.ml
  $ cp unit_functor.mlp unit_unapplied.mlp
  $ caravan --shh unit_unapplied.ml
  Verification successful.
  $ cp ../domains/functor_parameters.ml parameters.ml
  $ cat ../domains/functor_parameters.mlp unit_resource.mlp > parameters.mlp
  $ caravan --shh parameters.ml
  Verification successful.
  $ cp ../domains/functor_curried.ml curried.ml
  $ cat ../domains/functor_curried.mlp unit_resource.mlp > curried.mlp
  $ caravan --shh curried.ml
  Verification successful.
  $ cp ../domains/functor_raises.ml raises.ml
  $ cat ../domains/functor_raises.mlp unit_resource.mlp > raises.mlp
  $ caravan --shh raises.ml
  Verification successful.
  $ cp ../domains/ghost_explicit_functor.ml ghosts.ml
  $ cat ../domains/ghost_explicit_functor.mlp unit_resource.mlp > ghosts.mlp
  $ caravan --shh ghosts.ml
  Verification successful.

A protected resource and its Mutex/Domain facades can be declared inside the
functor, retaining the generic carrier and applicative instance identity.

  $ caravan --shh domain_functor.ml
  Verification successful.
  $ caravan --shh --emit-rav domain_functor.ml > domain_functor.rav
  $ raven --shh domain_functor.rav
  Verification successful.
  $ sed '/^module Int =/,$d' domain_functor.ml > unapplied.ml
  $ sed '/^proof result = client/,$d' domain_functor.mlp > unapplied.mlp
  $ caravan --shh unapplied.ml
  Verification successful.

Distinct argument modules retain distinct task ownership, even with equal carriers.

  $ sed 's/module Again = Worker (Int)/module Other = struct type t = int end module Again = Worker (Other)/' domain_functor.ml > wrong_instance.ml
  $ cp domain_functor.mlp wrong_instance.mlp
  $ caravan --shh wrong_instance.ml > wrong_instance.out 2>&1
  [1]
  $ grep -q 'Verification Error: A precondition may not hold' wrong_instance.out

Checked views forward acquire/release effects and logically atomic contracts.
The context witnesses are implementation-independent bindings, not extra API arguments.

  $ caravan --shh module_context.ml
  Verification successful.
  $ caravan --shh --emit-rav module_context.ml > module_context.rav
  $ raven --shh module_context.rav
  Verification successful.

An interface cannot hide an implementation's acquired holdings.

  $ sed 's/Finset.union locks (Finset.singleton mutex)/locks/g' module_context.ml > wrong_effect.ml
  $ cp module_context.mlp wrong_effect.mlp
  $ caravan --shh wrong_effect.ml > wrong_effect.out 2>&1
  [1]
  $ grep -q "The module argument does not establish this view's postcondition" wrong_effect.out

A generic caller still has to satisfy its own balanced exit contract.

  $ sed 's/O.release mutex;/if false then O.release mutex;/' module_context.ml > caller_leak.ml
  $ cp module_context.mlp caller_leak.mlp
  $ caravan --shh caller_leak.ml > caller_leak.out 2>&1
  [1]
  $ grep -q 'Verification Error: A postcondition may not hold' caller_leak.out

Imported operations preserve the context by framing it around their existing ABI.

  $ cp ../module_contracts/actual.mli actual.mli
  $ cp ../module_contracts/ordinary.ml imported.ml
  $ cp unit_resource.mlp imported.mlp
  $ caravan --shh imported.ml
  Verification successful.
  $ cp ../module_contracts/atomic.ml imported_atomic.ml
  $ cp unit_resource.mlp imported_atomic.mlp
  $ caravan --shh imported_atomic.ml
  Verification successful.

Polymorphic formal operations share the same forwarding machinery for native
and imported implementations, including logically atomic contracts.

  $ cp ../functor_polymorphism/argument.mli argument.mli
  $ cp ../functor_polymorphism/operations.ml polymorphic_operations.ml
  $ cp unit_resource.mlp polymorphic_operations.mlp
  $ caravan --shh polymorphic_operations.ml
  Verification successful.
  $ cp ../functor_polymorphism/atomic_argument.mli atomic_argument.mli
  $ cp ../functor_polymorphism/atomic.ml polymorphic_atomic.ml
  $ cp unit_resource.mlp polymorphic_atomic.mlp
  $ caravan --shh polymorphic_atomic.ml
  Verification successful.

Manual AU facades retain their source argument lists. Their tokens carry the
originating call's context through aliases, generic instances and ghost storage.

  $ cp ../proof_modules/scoped_au.ml scoped_au.ml
  $ cat ../proof_modules/scoped_au.mlp unit_resource.mlp > scoped_au.mlp
  $ caravan --shh scoped_au.ml
  Verification successful.
  $ cp ../polymorphic_ghost/au_functor.ml au_functor.ml
  $ cat ../polymorphic_ghost/au_functor.mlp unit_resource.mlp > au_functor.mlp
  $ caravan --shh au_functor.ml
  Verification successful.
  $ caravan --shh --emit-rav au_functor.ml > au_functor.rav
  $ raven --shh au_functor.rav
  Verification successful.
