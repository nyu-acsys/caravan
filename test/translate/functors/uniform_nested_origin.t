Functors declared in distinct enclosing instances retain their lexical arguments.

  $ caravan --shh uniform_nested_origin.ml
  Verification successful.
  $ caravan --shh --emit-rav uniform_nested_origin.ml > emitted.rav
  $ raven --shh emitted.rav
  Verification successful.
