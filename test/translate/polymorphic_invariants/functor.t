A single generic invariant body serves repeated applications, aliases, and two payload types together.

  $ caravan --shh functor.ml
  Verification successful.
  $ caravan --shh --emit-rav functor.ml > functor.rav
  $ grep -c 'inv make_is_cell(' functor.rav
  1
  $ raven --shh functor.rav
  Verification successful.
