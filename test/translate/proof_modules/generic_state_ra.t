A generic state field may use the resource algebra of its functor argument.

  $ caravan --shh generic_state_ra.ml
  Verification successful.
  $ caravan --shh --emit-rav generic_state_ra.ml > generic_state_ra.rav
  $ raven --shh generic_state_ra.rav
  Verification successful.
  $ grep -c '^module Generic_' generic_state_ra.rav
  1
