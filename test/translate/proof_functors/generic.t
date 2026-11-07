The manual proof stays generic across distinct functor applications and an alias.

  $ caravan --shh generic.ml
  Verification successful.

  $ caravan --shh --emit-rav generic.ml > generic.rav
  $ raven --shh generic.rav
  Verification successful.

The generic proof predicate and lemma have one source definition each.

  $ grep -c '^  pred .*wrapped' generic.rav
  1
  $ grep -c '^  lemma .*preserve' generic.rav
  1
  $ grep -c '^module Generic_Make_Cell' generic.rav
  1
  $ grep -c '^module Applied' generic.rav
  2

A named witness can be inferred through the generic predicate and lemma.

  $ caravan --shh witness.ml
  Verification successful.

  $ caravan --shh --emit-rav witness.ml > witness.rav
  $ raven --shh witness.rav
  Verification successful.

An incorrect generic lemma is rejected.

  $ cp generic.ml wrong_lemma.ml
  $ caravan --shh wrong_lemma.ml 2>&1 | grep -c 'Verification Error: A postcondition may not hold at this return point.'
  2
  $ caravan --shh wrong_lemma.ml 2>&1 | grep -c '\[Error\] File "wrong_lemma.proof"'
  1

The runtime result must satisfy the generic contract.

  $ cp generic.proof bad_body.proof
  $ caravan --shh bad_body.ml 2>&1 | grep -c 'Verification Error: A postcondition may not hold at this return point.'
  1

A later argument with a stronger read precondition cannot satisfy the template.

  $ sed 's/Actual.Second/Actual.Strong/g' generic.ml > later_argument_fail.ml
  $ cp generic.proof later_argument_fail.proof
  $ caravan --shh later_argument_fail.ml 2>&1 | grep -c "Verification Error: The module argument's precondition is not provided by this view."
  1

Private predicates also appear in contracts between generic methods.

  $ caravan --shh contracts.ml
  Verification successful.

The worker body mentions only its formal parameter, without concrete argument resources.

  $ ! sed -n '/^module Generic_Make_Cell\[/,/^module Checked_first_Cell/p' generic.rav | grep -E 'Actual_(First|Second)\.'

An unapplied proof template is checked through its generic runtime declaration.

  $ caravan --shh unapplied.ml
  Verification successful.

Source aliases retain their types in generic proof signatures and unfold witnesses.

  $ caravan --shh alias.ml
  Verification successful.
  $ caravan --shh --emit-rav alias.ml > alias.rav
  $ raven --shh alias.rav
  Verification successful.
