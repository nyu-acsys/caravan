A named generic functor verifies one stateful counter worker for multiple applications.

  $ caravan --shh generic_state.ml
  Verification successful.
  $ caravan --shh --emit-rav generic_state.ml > generic_state.rav
  $ raven --shh generic_state.rav
  Verification successful.
  $ grep -c '^module Generic_' generic_state.rav
  1

The generic worker rejects an action that does not match its state transition.

  $ ! caravan --shh generic_state_action_fail.ml > generic_state_action_fail.out 2>&1
  $ grep -q 'Verification Error: The invariant' generic_state_action_fail.out
  $ ! grep -q 'Internal Error:' generic_state_action_fail.out
