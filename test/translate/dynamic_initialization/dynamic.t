Initializer-local checked bindings support empty, singleton, and longer sequences,
tuple results, successive bindings, and lexical shadowing.

  $ caravan --shh dynamic.ml
  Verification successful.

The generated checked helper, including its decreases measure, prints as Raven.

  $ caravan --shh --emit-rav dynamic.ml > emitted.rav
  $ raven --shh --typeonly emitted.rav
  Verification successful.
