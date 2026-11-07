  $ caravan --shh missing_ordinary_resource.ml
  [Error] File "missing_ordinary_resource.ml", line 3, columns 16-30:
  3 | let read cell = Cell.read cell
                      ^^^^^^^^^^^^^^
  Verification Error: A precondition may not hold for this call.
  File "./nested_cells.mli", line 11, columns 15-31:
  11 |       requires holds cell value
                      ^^^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]

  $ caravan --shh missing_atomic_resource.ml
  [Error] File "missing_atomic_resource.ml", line 3, columns 16-30:
  3 | let read cell = Cell.read cell
                      ^^^^^^^^^^^^^^
  Verification Error: A precondition may not hold for this call.
  File "./nested_cells.mli", line 30, columns 22-38:
  30 |       atomic requires holds cell value
                             ^^^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]

  $ caravan --shh missing_atomic_ticket.ml
  [Error] File "missing_atomic_ticket.ml", line 3, columns 16-30:
  3 | let read cell = Cell.read cell
                      ^^^^^^^^^^^^^^
  Verification Error: A precondition may not hold for this call.
  File "./nested_cells.mli", line 28, columns 30-47:
  28 |       requires shared cell && ticket cell count
                                     ^^^^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]

  $ caravan --shh wrong_result.ml
  [Error] File "wrong_result.ml", line 3, columns 52-52:
  3 | let read cell = Nested_cells.Nested.Atomic.read cell
                                                          ^
  Verification Error: A postcondition may not hold at this return point.
  File "wrong_result.ml", line 6, columns 79-89:
  6 |     ensures Cell.shared cell && Cell.ticket cell count && Cell.holds cell 1 && result = 2 *)
                                                                                     ^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ caravan --shh distinct_types.ml
  [Error] File "distinct_types.ml", line 1, columns 47-81:
  1 | let mix value = Nested_cells.Nested.Other.read (Nested_cells.Ordinary.make value)
                                                     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: This expression has type Nested_cells.Ordinary.t
  but an expression was expected of type Nested_cells.Nested.Other.t.
  [1]
