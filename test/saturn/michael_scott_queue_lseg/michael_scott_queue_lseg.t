  $ caravan --shh --smt-timeout=30000 michael_scott_queue_lseg.ml
  Verification successful.

The emitted proof parses and type-checks as standalone Raven.

  $ caravan --shh --emit-rav michael_scott_queue_lseg.ml > emitted.rav
  $ raven --shh --typeonly emitted.rav
  Verification successful.
