Loop invariants in proof outlines use named counters and earlier exports.

  $ caravan --shh loops.ml
  Verification successful.
  $ caravan --shh --emit-rav loops.ml > loops.rav
  $ raven --shh loops.rav
  Verification successful.

A loop invariant names the value of an existential after each iteration.

  $ caravan --shh witnesses.ml
  Verification successful.

  $ caravan --shh witnesses_fail.ml
  [Error] File "witnesses_fail.mlp", line 11, columns 11-16:
  11 |     with { value = Map.set values i i }
                  ^^^^^
  Type Error: This name is not bound by the loop's invariants.
  [1]

The names that witnesses bind are available in the loop's body, with their values at
the start of the iteration, and after the loop, but not before it.

  $ caravan --shh witness_scope.ml
  Verification successful.

  $ caravan --shh witness_scope_fail.ml
  [Error] File "witness_scope_fail.mlp", line 5, columns 20-26:
  5 |     assert (Map.get values 0 = 0);
                          ^^^^^^
  Type Error: Unbound value values.
  [1]

OCaml thunk anchors distinguish task spawns without extending logical terms.

  $ caravan --shh thunks.ml
  Verification successful.
  $ caravan --shh --emit-rav thunks.ml > thunks.rav
  $ raven --shh thunks.rav
  Verification successful.

Invalid loop placements and bindings report source errors.

  $ caravan --shh not_first.ml > not_first.out 2>&1
  [1]
  $ grep 'Type Error:' not_first.out
  Type Error: A loop invariant anchors the first expression of its loop body.
  $ caravan --shh ambiguous.ml > ambiguous.out 2>&1
  [1]
  $ grep -q 'Type Error: This anchor matches 2 places of loop' ambiguous.out
  $ caravan --shh duplicate.ml > duplicate.out 2>&1
  [1]
  $ grep 'Type Error:' duplicate.out
  Type Error: A loop has at most one annotation.
  $ caravan --shh effectful.ml > effectful.out 2>&1
  [1]
  $ grep 'Type Error:' effectful.out
  Type Error: An outline binding used by a loop invariant must be a logical expression.
