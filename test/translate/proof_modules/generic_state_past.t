Past facts in a generic state resolve in each application and its clients.

  $ caravan --shh generic_state_past.ml
  Verification successful.
  $ caravan --shh --emit-rav generic_state_past.ml > generic_state_past.rav
  $ raven --shh generic_state_past.rav
  Verification successful.
  $ grep -c '^module Generic_' generic_state_past.rav
  1

A function cannot return a history fact without a witness.

  $ ! caravan --shh generic_state_past_fail.ml > generic_state_past_fail.out 2>&1
  $ grep -q 'Verification Error: A postcondition may not hold' generic_state_past_fail.out
  $ ! grep -Eq 'Internal Error:|timed out|timeout' generic_state_past_fail.out
