Local helpers share their enclosing polymorphic worker inside a source functor,
including aliases and repeated applications.

  $ caravan --shh module.ml
  Verification successful.
  $ caravan --shh --emit-rav module.ml > module.rav
  $ grep -c 'Generic_.*\[Parameter:' module.rav
  1
  $ grep -c 'proc .*step' module.rav
  1
  $ raven --shh module.rav
  Verification successful.
