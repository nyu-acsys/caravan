A generic mutable record shares its stateful allocation proof across applications.

  $ caravan --shh generic_state_record.ml
  Verification successful.
  $ caravan --shh --emit-rav generic_state_record.ml > generic_state_record.rav
  $ raven --shh generic_state_record.rav
  Verification successful.
  $ grep -c 'Generic_.*\[Parameter:' generic_state_record.rav
  1
