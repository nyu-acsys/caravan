Exceptions are the constructors of one data type: values of type exn are built and
matched like those of a variant, with their payloads' domains.

  $ caravan --shh values.ml
  Verification successful.

A function that may raise returns the exception it raised, and a caller propagates it,
with what its raises clauses say holds.

  $ caravan --shh raise.ml
  Verification successful.

Helpers without a contract raise what their bodies and calls raise; predefined
exceptions raise as declared ones.

  $ caravan --shh inferred.ml
  Verification successful.

Exceptions of different modules with the same name are different, as are those of a
functor's applications, which each declare their own.

  $ caravan --shh same_names.ml
  Verification successful.
  $ caravan --shh functor_applications.ml
  Verification successful.

Exceptions of modules, of generic functions at several types, and of an interface.

  $ caravan --shh modules.ml
  Verification successful.
  $ caravan --shh generic.ml
  Verification successful.
  $ caravan --shh box.ml
  Verification successful.

The emitted program verifies too.

  $ caravan --shh --emit-rav raise.ml > raise.rav
  $ raven --shh raise.rav
  Verification successful.

Handlers catch the exceptions of their protected part: the rest of the part does not run
after a raise, an exception no case catches propagates, a handler can re-raise what it
caught, and a function whose handler catches everything raises nothing.

  $ caravan --shh handlers.ml
  Verification successful.
  $ caravan --shh --emit-rav handlers.ml > handlers.rav
  $ raven --shh handlers.rav
  Verification successful.
  $ caravan --shh handler_helper.ml
  Verification successful.

A match's exception cases catch the scrutinee's exceptions, not its value cases'.

  $ caravan --shh match_exception.ml
  Verification successful.

A loop that may raise stops when it does, and the exception then propagates. Its
invariant holds while it has not raised; when it has, the function's raises clauses hold
if the exception leaves the function, or the loop's own raises clauses.

  $ caravan --shh loops.ml
  Verification successful.
  $ caravan --shh --emit-rav loops.ml > loops.rav
  $ raven --shh loops.rav
  Verification successful.

A function with an atomic contract linearizes by raising: the step that linearizes it
commits its update with the exception the function then raises, which its atomic raises
clauses describe. Clients catch it, or propagate it with its state.

  $ caravan --shh atomic_stack.ml
  Verification successful.
  $ mkdir clients
  $ cp atomic_stack.ml atomic_stack.mli atomic_stack.proof clients/
  $ chmod u+w clients/atomic_stack.ml
  $ cat atomic_stack_clients.ml >> clients/atomic_stack.ml
  $ caravan --shh clients/atomic_stack.ml
  Verification successful.
