A proof outline gives a function's proof in the .proof file, as steps at its code:
ghost code on return, and a linearization at an atomic access, which an anchor names
with the code's own names, or as the code bound to a name.

  $ caravan --shh cells.ml
  Verification successful.

A step can export a value to the later steps, as let p = at (code) (fun step -> e),
whose scope returns the value with the result, and the outline can bind pure ghost code
for them, as let x = e. A step uses an export only if the code exporting it runs on
every path to it; the earlier steps' state is not threaded through scopes.

  $ caravan --shh exports.ml
  Verification successful.

  $ caravan --shh conditional_export.ml
  [Error] File "conditional_export.proof", line 11, column 28 to line 16, column 11:
  11 |   at (let b = Atomic.get c) (fun step ->
                                   ^^^^^^^^^^^^
  Type Error: The step exporting first, at line 7 of the code, does not run on every path to this step.
  [1]

  $ caravan --shh export_shape.ml
  [Error] File "export_shape.proof", line 10, columns 4-10:
  10 |     result) in
           ^^^^^^
  Type Error: A scope that exports a value returns (unchanged operation result, value).
  [1]

  $ caravan --shh state_binder.ml
  [Error] File "state_binder.proof", line 6, columns 38-40:
  6 |   at (let a = Atomic.get c) (fun step () ->
                                            ^^
  Syntax Error: A step exports a value for later steps as let p = at (code) (fun step -> e).
  [1]

Errors in a step's code are reported where the outline writes it.

  $ caravan --shh step_error.ml
  [Error] File "step_error.proof", line 4, columns 24-25:
  4 |   on return fold cell c w
                              ^
  Type Error: Unbound value w.
  [1]

An anchor must match exactly one place after the previous step.

  $ caravan --shh ambiguous_anchor.ml
  [Error] File "ambiguous_anchor.proof", line 7, columns 18-30:
  7 | proof twice = at (Atomic.get c) commit
                        ^^^^^^^^^^^^
  Type Error: This anchor matches 2 places of twice, at 5:14, 5:29.
  [1]

  $ caravan --shh unmatched_anchor.ml
  [Error] File "unmatched_anchor.proof", line 5, columns 16-28:
  5 | proof get = at (Atomic.get d) commit
                      ^^^^^^^^^^^^
  Type Error: This anchor matches no code of get after the previous step.
  [1]

An outline names a function of the program, by its parameters if several have its name.

  $ caravan --shh unknown_function.ml
  [Error] File "unknown_function.proof", line 3, columns 6-9:
  3 | proof set = at (Atomic.get c) commit
            ^^^
  Type Error: The program defines no function set.
  [1]

  $ caravan --shh shadowed.ml
  [Error] File "shadowed.proof", line 5, columns 6-9:
  5 | proof get = at (Atomic.get c) commit
            ^^^
  Type Error: Several functions are named get; list the parameters of the one this proves.
  [1]

  $ caravan --shh parameters.ml
  [Error] File "parameters.proof", line 3, columns 6-9:
  3 | proof get c d = at (Atomic.get c) commit
            ^^^
  Type Error: The function get has 1 parameter.
  [1]

A program whose proofs are outlines has no annotations, and one outline per function.

  $ caravan --shh mixed.ml
  [Error] File "mixed.ml", line 5, columns 0-20:
  5 | (*@ fold cell c v *)
      ^^^^^^^^^^^^^^^^^^^^
  Type Error: A program whose proofs are outlines in its .proof file has no proof annotations.
  [1]

  $ caravan --shh duplicate.ml
  [Error] File "duplicate.proof", line 5, columns 6-9:
  5 | proof get = at (Atomic.get c) commit
            ^^^
  Type Error: This function has another outline.
  [1]

  $ caravan --shh bad_step.ml
  [Error] File "bad_step.proof", line 3, columns 12-17:
  3 | proof get = after (Atomic.get c) commit
                  ^^^^^
  Syntax Error: A step is at (code) followed by its step, or on return followed by ghost code.
  [1]
