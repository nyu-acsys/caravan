Named and constructed payloads, nested tuples, and record-label boundaries keep
independent field and primitive identities.

  $ caravan --shh field_identities.ml
  Verification successful.
  $ caravan --shh --emit-rav field_identities.ml > field_identities.rav
  $ raven --shh field_identities.rav
  Verification successful.
