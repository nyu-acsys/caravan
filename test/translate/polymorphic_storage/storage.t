Generic allocation, access and updates share constrained fields with concrete clients.

  $ caravan --shh storage.ml
  Verification successful.
  $ caravan --shh --emit-rav storage.ml > storage.rav
  $ raven --shh storage.rav
  Verification successful.
