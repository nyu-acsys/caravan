A mutex registration nested in a public invariant needs no opening credit of
its own: native lock operations transfer the resource without unfolding it.
The caller explicitly reserves the public invariant family.

  $ caravan --shh nested_registration.ml
  Verification successful.
