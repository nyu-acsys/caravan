Manual atomic updates preserve local exception identities in fresh functor applications.

  $ caravan --shh functor.ml
  Verification successful.
  $ caravan --shh --emit-rav functor.ml > functor.rav
  $ raven --shh functor.rav
  Verification successful.
