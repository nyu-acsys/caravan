Sibling stateful invariants, views and actions use their owning module's proof
environment, including through aliases.

  $ caravan --shh scoped_state.ml
  Verification successful.
  $ caravan --shh --emit-rav scoped_state.ml > scoped_state.rav
  $ raven --shh scoped_state.rav
  Verification successful.

State fields retain their declaration types when inherited or qualified.

  $ caravan --shh scoped_state_inherited.ml
  Verification successful.

Past facts resolve the state in their own module.

  $ caravan --shh scoped_state_past.ml
  Verification successful.
  $ caravan --shh --history=monotone scoped_state_past.ml
  Verification successful.

A past fact still requires its invariant, even when no view is mentioned.

  $ mkdir no_invariant
  $ cp scoped_state_past.proof no_invariant/
  $ sed 's/requires live root/requires true/' scoped_state_past.ml > no_invariant/scoped_state_past.ml
  $ caravan --shh no_invariant/scoped_state_past.ml 2>&1 | grep -F 'which the precondition does not hold.'
  Type Error: A fact about an earlier state of left_live, which the precondition does not hold.
