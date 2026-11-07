Generic immutable wrappers use their contained atomic as the shared structure's anchor.

  $ caravan --shh record.ml
  Verification successful.
  $ caravan --shh --emit-rav record.ml > record.rav
  $ raven --shh record.rav
  Verification successful.
