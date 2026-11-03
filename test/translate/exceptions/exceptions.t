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
