Static modules and source functors share generic function workers while retaining
named module-parameter types independently of function type parameters.

  $ caravan --shh modules.ml
  Verification successful.
  $ caravan --shh --emit-rav modules.ml > modules.rav
  $ raven --shh modules.rav
  Verification successful.
