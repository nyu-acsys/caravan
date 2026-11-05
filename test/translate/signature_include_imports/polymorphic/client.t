Included parameterized types share their declaration variables with inherited
polymorphic predicates and functions, independently for each namespace.

  $ caravan --shh client.ml
  Verification successful.

  $ caravan --shh --emit-rav client.ml > emitted.rav
  $ raven --shh --typeonly emitted.rav
  Verification successful.
