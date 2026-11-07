Unit-functor instances preserve native type identities while inferring witness-selected
atomic update headers and source annotation variables.

  $ caravan --shh witness_functor.ml
  Verification successful.

  $ caravan --shh --emit-rav witness_functor.ml > emitted.rav
  $ raven --shh --typeonly emitted.rav
  Verification successful.
