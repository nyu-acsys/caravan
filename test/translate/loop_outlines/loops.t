Loop invariants in proof outlines use named counters and earlier exports.

  $ caravan --shh loops.ml
  Verification successful.
  $ caravan --shh --emit-rav loops.ml > loops.rav
  $ raven --shh loops.rav
  Verification successful.

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
