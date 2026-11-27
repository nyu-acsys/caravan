One-shot predictions use Raven's prophecy resources, including through predicates
and polymorphic lemmas.

  $ caravan --shh one_shot.ml
  Verification successful.

The generated program preserves prophecy semantics when parsed by Raven.

  $ caravan --shh --emit-rav one_shot.ml > one_shot.rav
  $ raven --shh one_shot.rav
  Verification successful.

Resolving twice requires a resource that the first resolution consumed.

  $ cp one_shot.ml twice.ml
  $ sed '/Ghost.Prophecy.resolve prophecy result;/a\
  > \    Ghost.Prophecy.resolve prophecy result;' one_shot.mlp > twice.mlp
  $ caravan --shh --only observe twice.ml > twice.out 2>&1
  [1]
  $ grep -q 'Verification Error:' twice.out
  $ grep -qi timeout twice.out
  [1]

A predicted value is not known before resolution.

  $ cp one_shot.ml early.ml
  $ sed '/Ghost.Prophecy.resolve prophecy result;/i\
  > \    assert (predicted);' one_shot.mlp > early.mlp
  $ caravan --shh --only observe early.ml > early.out 2>&1
  [1]
  $ grep -q 'Verification Error:' early.out
  $ grep -qi timeout early.out
  [1]

Resolution must have the prophecy's payload type.

  $ cp one_shot.ml wrong_type.ml
  $ sed 's/Ghost.Prophecy.resolve prophecy result;/Ghost.Prophecy.resolve prophecy 0;/' one_shot.mlp > wrong_type.mlp
  $ caravan --shh wrong_type.ml > wrong_type.out 2>&1
  [1]
  $ grep -q 'Type Error:' wrong_type.out

A prediction must be resolved before it can agree with an observed value.

  $ cp one_shot.ml unresolved.ml
  $ sed '/Ghost.Prophecy.resolve prophecy result;/d' one_shot.mlp > unresolved.mlp
  $ caravan --shh --only observe unresolved.ml > unresolved.out 2>&1
  [1]
  $ grep -q 'Verification Error:' unresolved.out
  $ grep -qi timeout unresolved.out
  [1]
