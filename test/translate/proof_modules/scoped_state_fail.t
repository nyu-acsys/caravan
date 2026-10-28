Scoped actions reject a compare-and-set that does not match their transition.

  $ caravan --shh scoped_state_action_fail.ml 2>&1 | grep -F 'This step may not perform the action counter_set_step.'
  Verification Error: This step may not perform the action counter_set_step.

The declared view value type is checked against the proof definition.

  $ caravan --shh scoped_state_view_fail.ml 2>&1 | grep -A3 -F 'Type Error: Expected an expression of type'
  Type Error: Expected an expression of type
    Int
  but found an expression of type
    Bool.

A state type defined inside an ascribed module is private to that module.

  $ caravan --shh scoped_state_private_fail.ml 2>&1 | grep -F 'The state is private to its module.'
  Type Error: The state is private to its module.

An action must identify one invariant in its owning scope.

  $ caravan --shh scoped_state_ambiguous_fail.ml 2>&1 | grep -F 'Several stateful invariants match this action'
  Type Error: Several stateful invariants match this action: use distinct state binders.
