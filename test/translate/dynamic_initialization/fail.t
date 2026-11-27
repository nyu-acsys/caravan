Invalid dynamic initializers fail at the annotated constructor.

  $ cp dynamic.mlp duplicate.mlp
  $ caravan --shh duplicate.ml
  [Error] File "duplicate.ml", line 7, columns 24-48:
  7 | (*@ initially { cells = to_sequence [cell; cell]; size = 2 } *)
                              ^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: The cells of this indexed field may not be distinct.
  Related Location: This assertion may not hold
  [1]

  $ cp dynamic.mlp wrong_value.mlp
  $ caravan --shh wrong_value.ml
  [Error] File "wrong_value.ml", line 5, columns 15-15:
  5 |   Atomic.make 0
                     ^
  Verification Error: The invariant valid may not hold when this function returns.
  File "wrong_value.mlp", line 3, columns 10-15:
  3 | invariant valid (q : t) (s : state) =
                ^^^^^
  Related Location: The invariant.
  [1]

  $ cp dynamic.mlp missing_ownership.mlp
  $ caravan --shh missing_ownership.ml
  [Error] File "missing_ownership.ml", line 3, columns 48-48:
  3 | let create (cell : int Atomic.t) = Atomic.make 0
                                                      ^
  Verification Error: The invariant valid may not hold when this function returns.
  File "missing_ownership.mlp", line 3, columns 10-15:
  3 | invariant valid (q : t) (s : state) =
                ^^^^^
  Related Location: The invariant.
  [1]

  $ cp dynamic.mlp wrong_size.mlp
  $ caravan --shh wrong_size.ml
  [Error] File "wrong_size.ml", line 5, columns 15-15:
  5 |   Atomic.make 0
                     ^
  Verification Error: The invariant valid may not hold when this function returns.
  File "wrong_size.mlp", line 3, columns 10-15:
  3 | invariant valid (q : t) (s : state) =
                ^^^^^
  Related Location: The invariant.
  [1]

  $ cp dynamic.mlp wrong_type.mlp
  $ caravan --shh wrong_type.ml
  [Error] File "wrong_type.ml", line 5, columns 24-39:
  5 | (*@ initially { cells = to_sequence [1]; size = 1 } *)
                              ^^^^^^^^^^^^^^^
  Type Error: This expression has type int sequence but an expression was expected of type
    int Atomic.t sequence
  Type int is not compatible with type int Atomic.t.
  [1]

  $ cp dynamic.mlp duplicate_field.mlp
  $ caravan --shh duplicate_field.ml
  [Error] File "duplicate_field.ml", line 5, columns 72-76:
  5 | (*@ initially { cells = to_sequence ([] : int Atomic.t list); size = 0; size = 1 } *)
                                                                              ^^^^
  Type Error: The initial field size is given twice.
  [1]

  $ cp dynamic.mlp unknown_field.mlp
  $ caravan --shh unknown_field.ml
  [Error] File "unknown_field.ml", line 5, columns 72-76:
  5 | (*@ initially { cells = to_sequence ([] : int Atomic.t list); size = 0; typo = 0 } *)
                                                                              ^^^^
  Type Error: Unknown initial state field typo.
  [1]

  $ cp dynamic.mlp missing_field.mlp
  $ caravan --shh missing_field.ml
  [Error] File "missing_field.ml", line 5, columns 0-65:
  5 | (*@ initially { cells = to_sequence ([] : int Atomic.t list) } *)
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: The initial state has no field size.
  [1]

  $ cp dynamic.mlp leak.mlp
  $ caravan --shh leak.ml
  [Error] File "leak.ml", line 7, columns 18-23:
  7 | (*@ proof assert (cells === []) *)
                        ^^^^^
  Type Error: Unbound name cells.
  [1]
