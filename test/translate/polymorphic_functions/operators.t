Polymorphic operator names and their specification calls share ordinary workers.

  $ caravan --shh operators.ml
  Verification successful.
  $ caravan --shh --emit-rav operators.ml > operators.rav
  $ raven --shh operators.rav
  Verification successful.
