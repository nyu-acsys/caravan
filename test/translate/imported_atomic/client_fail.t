The atomic precondition is checked, and the atomic postcondition constrains results.

  $ caravan --shh missing_resource.ml
  [Error] File "missing_resource.ml", line 1, columns 16-37:
  1 | let read cell = Atomic_cell.read cell
                      ^^^^^^^^^^^^^^^^^^^^^
  Verification Error: A precondition may not hold for this call.
  File "./atomic_cell.mli", line 15, columns 20-36:
  15 |     atomic requires holds cell value
                           ^^^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]

  $ caravan --shh wrong_post.ml
  [Error] File "wrong_post.ml", line 1, columns 37-37:
  1 | let read cell = Atomic_cell.read cell
                                           ^
  Verification Error: A postcondition may not hold at this return point.
  File "wrong_post.ml", line 5, columns 12-22:
  5 |     ensures result = 2 *)
                  ^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

Ordinary preconditions are required independently of the atomic resource.

  $ caravan --shh missing_ordinary.ml
  [Error] File "missing_ordinary.ml", line 1, columns 16-37:
  1 | let read cell = Atomic_cell.read cell
                      ^^^^^^^^^^^^^^^^^^^^^
  Verification Error: A precondition may not hold for this call.
  File "./atomic_cell.mli", line 13, columns 28-45:
  13 |     requires shared cell && ticket cell count
                                   ^^^^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]

Ordinary preconditions cannot be borrowed from an open invariant across the call.

  $ caravan --shh ordinary_invariant.ml
  [Error] File "ordinary_invariant.ml", line 1, columns 16-37:
  1 | let read cell = Atomic_cell.read cell
                      ^^^^^^^^^^^^^^^^^^^^^
  Verification Error: A precondition may not hold for this call.
  File "./atomic_cell.mli", line 13, columns 28-45:
  13 |     requires shared cell && ticket cell count
                                   ^^^^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]

Predicate declarations must match ordinary predicate definitions.

  $ caravan --shh invariant_mismatch.ml
  [Error] File "invariant_mismatch.proof", line 1, columns 10-14:
  1 | invariant held (cell : t) = own cell.contents 0
                ^^^^
  Type Error: The predicate held must be defined as an ordinary predicate.
  File "invariant_mismatch.mli", line 3, columns 0-32:
  3 | (*@ predicate held (cell : t) *)
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: Its declaration.
  [1]

Invariant declarations use the invariant keyword.

  $ caravan --shh old_syntax.ml
  [Error] File "old_syntax.mli", line 1, columns 36-49:
  1 | (*@ predicate held (cell : int ref) [@persistent] *)
                                          ^^^^^^^^^^^^^
  Syntax Error: Syntax error.
  [1]
