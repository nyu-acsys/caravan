Companion declarations expose named predicates through an annotation-free signature.

  $ caravan --shh companion_predicates.ml
  Verification successful.

Predicates absent from the companion interface remain hidden.

  $ cp companion_predicates.ml companion_predicates_hidden_fail.ml
  $ cp companion_predicates.mli companion_predicates_hidden_fail.mli
  $ cat companion_predicates.proof > companion_predicates_hidden_fail.proof
  $ printf '\nlemma leak (value : Box.t) requires (Box.hidden value) = ()\n' >> companion_predicates_hidden_fail.proof
  $ ! caravan --shh companion_predicates_hidden_fail.ml > hidden.out 2>&1
  $ grep -q 'A call of a function in a contract' hidden.out

An exposed predicate's definition remains opaque.

  $ cp companion_predicates.ml companion_predicates_opaque_fail.ml
  $ cp companion_predicates.mli companion_predicates_opaque_fail.mli
  $ cat companion_predicates.proof > companion_predicates_opaque_fail.proof
  $ printf '\nlemma leak (value : Box.t) requires (Box.visible value) ensures (Box.visible value) =\n  unfold Box.visible value;\n  fold Box.visible value\n' >> companion_predicates_opaque_fail.proof
  $ ! caravan --shh companion_predicates_opaque_fail.ml > opaque.out 2>&1
  $ grep -q 'The definition of this predicate is hidden by its module signature' opaque.out

An annotated source signature retains its explicit predicate boundary.

  $ ! caravan --shh companion_predicates_annotated_fail.ml > annotated.out 2>&1
  $ grep -q 'A call of a function in a contract' annotated.out
