Earlier partial applications remain available when a later one is completed first.

  $ caravan --shh uniform_argument_order.ml
  Verification successful.
  $ caravan --shh --emit-rav uniform_argument_order.ml > emitted.rav
  $ raven --shh emitted.rav
  Verification successful.
