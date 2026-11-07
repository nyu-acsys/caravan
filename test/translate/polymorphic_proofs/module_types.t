Parameterized mathematical datatypes retain their parameters and carriers in static
modules and shared source-functor layouts.

  $ caravan --shh module_types.ml
  Verification successful.
  $ caravan --shh --emit-rav module_types.ml > module_types.rav
  $ grep -c 'Generic_.*\[Parameter:' module_types.rav
  1
  $ raven --shh module_types.rav
  Verification successful.
