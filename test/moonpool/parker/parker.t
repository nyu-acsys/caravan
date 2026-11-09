The upstream Parker implementation verifies with an abstract coalescing permit.

  $ caravan --shh parker_.ml
  Verification successful.
  $ caravan --shh --emit-rav parker_.ml > parker.rav
  $ raven --shh parker.rav
  Verification successful.
