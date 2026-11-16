Inline folds verify tuple accumulators, effectful callbacks, callback proof scopes,
and inherited ghost state.

  $ caravan --shh fold.ml
  Verification successful.

Exceptions raised in callbacks propagate through the fold and can be handled.

  $ caravan --shh raises.ml
  Verification successful.

Stateful tuple operands execute right to left and thread state into their continuation.
Their state stays local when the tuple is an ordinary function argument.

  $ caravan --shh tuple_state.ml
  Verification successful.

Record construction threads state through its field operands and continuation.

  $ caravan --shh record_state.ml
  Verification successful.

An atomic allocation's scope receives the state of its explicitly scoped operand.

  $ caravan --shh nested_atomic.ml
  Verification successful.

Visibility weakening checks its subset premise and retains both seen views.

  $ caravan --shh weaken.ml
  Verification successful.

The invariant must hold at fold entry.

  $ caravan --shh bad_invariant.ml
  [Error] File "bad_invariant.proof", line 3, columns 44-59:
  3 |     invariant (fun accumulator remaining -> accumulator = 1)
                                                  ^^^^^^^^^^^^^^^
  Verification Error: This loop invariant may not hold upon loop entry.
  File "bad_invariant.proof", line 3, columns 44-59:
  3 |     invariant (fun accumulator remaining -> accumulator = 1)
                                                  ^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

Dynamically selected callbacks and partial applications are rejected.

  $ caravan --shh dynamic.ml
  [Error] File "dynamic.ml", line 3, column 4 to line 4, column 48:
  3 |     (if choose then fun accumulator _value -> accumulator
          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Unsupported Error: A List.fold_left callback other than an inline function with two parameters is not supported yet.
  [1]

  $ caravan --shh partial.ml
  [Error] File "partial.ml", line 2, columns 13-69:
  2 |   let fold = List.fold_left (fun accumulator _value -> accumulator) 0 in
                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Unsupported Error: A partially applied List.fold_left; supply all three arguments is not supported yet.
  [1]
