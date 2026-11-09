Unit, named-parameter, curried and exceptional Domain functors use the same
execution boundary as ordinary procedures.

  $ cp ../domains/functor.ml unit_functor.ml
  $ cat ../domains/functor.proof unit_resource.proof > unit_functor.proof
  $ caravan --shh unit_functor.ml
  Verification successful.
  $ sed '/^module First =/,$d' unit_functor.ml > unit_unapplied.ml
  $ cp unit_functor.proof unit_unapplied.proof
  $ caravan --shh unit_unapplied.ml
  Verification successful.
  $ cp ../domains/functor_parameters.ml parameters.ml
  $ cat ../domains/functor_parameters.proof unit_resource.proof > parameters.proof
  $ caravan --shh parameters.ml
  Verification successful.
  $ cp ../domains/functor_curried.ml curried.ml
  $ cat ../domains/functor_curried.proof unit_resource.proof > curried.proof
  $ caravan --shh curried.ml
  Verification successful.
  $ cp ../domains/functor_raises.ml raises.ml
  $ cat ../domains/functor_raises.proof unit_resource.proof > raises.proof
  $ caravan --shh raises.ml
  Verification successful.
  $ cp ../domains/ghost_explicit_functor.ml ghosts.ml
  $ cat ../domains/ghost_explicit_functor.proof unit_resource.proof > ghosts.proof
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
  $ sed '/^proof result = client/,$d' domain_functor.proof > unapplied.proof
  $ caravan --shh unapplied.ml
  Verification successful.

Distinct argument modules retain distinct task ownership, even with equal carriers.

  $ sed 's/module Again = Worker (Int)/module Other = struct type t = int end module Again = Worker (Other)/' domain_functor.ml > wrong_instance.ml
  $ cp domain_functor.proof wrong_instance.proof
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
  $ cp module_context.proof wrong_effect.proof
  $ caravan --shh wrong_effect.ml > wrong_effect.out 2>&1
  [1]
  $ grep -q "The module argument does not establish this view's postcondition" wrong_effect.out

A generic caller still has to satisfy its own balanced exit contract.

  $ sed 's/O.release mutex;/if false then O.release mutex;/' module_context.ml > caller_leak.ml
  $ cp module_context.proof caller_leak.proof
  $ caravan --shh caller_leak.ml > caller_leak.out 2>&1
  [1]
  $ grep -q 'Verification Error: A postcondition may not hold' caller_leak.out

Imported operations preserve the context by framing it around their existing ABI.

  $ cp ../module_contracts/actual.mli actual.mli
  $ cp ../module_contracts/ordinary.ml imported.ml
  $ cp unit_resource.proof imported.proof
  $ caravan --shh imported.ml
  Verification successful.
  $ cp ../module_contracts/atomic.ml imported_atomic.ml
  $ cp unit_resource.proof imported_atomic.proof
  $ caravan --shh imported_atomic.ml
  Verification successful.

Polymorphic formal operations share the same forwarding machinery for native
and imported implementations, including logically atomic contracts.

  $ cp ../functor_polymorphism/argument.mli argument.mli
  $ cp ../functor_polymorphism/operations.ml polymorphic_operations.ml
  $ cp unit_resource.proof polymorphic_operations.proof
  $ caravan --shh polymorphic_operations.ml
  Verification successful.
  $ cp ../functor_polymorphism/atomic_argument.mli atomic_argument.mli
  $ cp ../functor_polymorphism/atomic.ml polymorphic_atomic.ml
  $ cp unit_resource.proof polymorphic_atomic.proof
  $ caravan --shh polymorphic_atomic.ml
  Verification successful.

Manual AU facades retain their source argument lists. Their tokens carry the
originating call's context through aliases, generic instances and ghost storage.

  $ cp ../proof_modules/scoped_au.ml scoped_au.ml
  $ cat ../proof_modules/scoped_au.proof unit_resource.proof > scoped_au.proof
  $ caravan --shh scoped_au.ml
  Verification successful.
  $ cp ../polymorphic_ghost/au_functor.ml au_functor.ml
  $ cat ../polymorphic_ghost/au_functor.proof unit_resource.proof > au_functor.proof
  $ caravan --shh au_functor.ml
  Verification successful.
  $ caravan --shh --emit-rav au_functor.ml > au_functor.rav
  $ raven --shh au_functor.rav
  Verification successful.
