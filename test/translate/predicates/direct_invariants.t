Direct invariants retain all parameters and can be established in checked lemmas.
Their existential witnesses can be bound by name while unfolding.

  $ caravan --shh direct_invariants.ml
  Verification successful.

Implicit invariant parameters are fixed by the folded invariant instance.

  $ caravan --shh implicit_invariants.ml
  Verification successful.
  $ cp implicit_invariants.ml implicit_invariant_change.ml
  $ caravan --shh --only change implicit_invariant_change.ml > changed.out 2>&1
  [1]
  $ grep -q 'Verification Error:' changed.out
  $ grep -qi timeout changed.out
  [1]
