Parameterized immutable data preserve carrier identity through static aliases and
repeated applicative source-functor applications.

  $ caravan --shh modules.ml
  Verification successful.
  $ caravan --shh --emit-rav modules.ml > modules.rav
  $ grep -c 'Generic_.*\[Parameter:' modules.rav
  1
  $ raven --shh modules.rav
  Verification successful.
