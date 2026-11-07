Distinct generic state applications keep separate invariant tokens even when their OCaml cell types agree.

  $ ! caravan --shh generic_state_interchange_fail.ml > generic_state_interchange_fail.out 2>&1
  $ grep -q 'The invariant make_is_counter required by method_set_one is not available' generic_state_interchange_fail.out
  $ ! grep -q 'Internal Error:' generic_state_interchange_fail.out

A sealed application hides its state type from root proof declarations.

  $ ! caravan --shh generic_state_private_state_fail.ml > generic_state_private_state_fail.out 2>&1
  $ grep -q 'Type Error: Unbound type constructor One.state.' generic_state_private_state_fail.out

A sealed application hides its action from root source annotations.

  $ ! caravan --shh generic_state_private_action_fail.ml > generic_state_private_action_fail.out 2>&1
  $ grep -q 'Type Error: There is no action set_one.' generic_state_private_action_fail.out

A sealed application hides its private proof helper from root proof declarations.

  $ ! caravan --shh generic_state_private_helper_fail.ml > generic_state_private_helper_fail.out 2>&1
  $ grep -q 'Type Error: Unknown lemma One.private_helper.' generic_state_private_helper_fail.out
