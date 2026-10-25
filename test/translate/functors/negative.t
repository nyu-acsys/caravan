  $ caravan --shh hidden_post_fail.ml
  [Error] File "hidden_post_fail.ml", line 12, columns 26-26:
  12 |   let read x = Cell.read x
                                 ^
  Verification Error: A postcondition may not hold at this return point.
  File "hidden_post_fail.ml", line 15, columns 38-52:
  15 |       ensures Cell.counter x state && result = state *)
                                             ^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ caravan --shh bad_argument_fail.ml
  [Error] File "bad_argument_fail.ml", line 14, columns 16-42:
  14 | module Client = Make (Actual.Strong_First)
                       ^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: The module argument's precondition is not provided by this view.
  File "bad_argument_fail.ml", line 5, columns 2-21:
  5 |   val read : t -> int
        ^^^^^^^^^^^^^^^^^^^
  Related Location: The requested module operation.
  File "./actual.mli", line 35, columns 2-21:
  35 |   val read : t -> int
         ^^^^^^^^^^^^^^^^^^^
  Related Location: The actual module operation.
  [1]

  $ caravan --shh unit_fail.ml
  [Error] File "unit_fail.ml", line 1, column 12 to line 3, column 3:
  1 | module Make () = struct
                  ^^^^^^^^^^^
  Unsupported Error: A unit functor is not supported yet.
  [1]

  $ caravan --shh higher_order_fail.ml
  [Error] File "higher_order_fail.ml", line 5, columns 25-48:
  5 | module Make (F : functor (Cell : Value) -> Value) = struct
                               ^^^^^^^^^^^^^^^^^^^^^^^
  Unsupported Error: A functor signature is not supported yet.
  [1]

  $ caravan --shh anonymous_argument_fail.ml
  [Error] File "anonymous_argument_fail.ml", line 9, column 22 to line 11, column 3:
  9 | module Client = Make (struct
                            ^^^^^^
  Unsupported Error: A non-path functor argument is not supported yet.
  [1]

  $ caravan --shh curried_fail.ml
  [Error] File "curried_fail.ml", line 5, column 27 to line 7, column 3:
  5 | module Make (Left : Value) (Right : Value) = struct
                                 ^^^^^^^^^^^^^^^^^^^^^^^^
  Unsupported Error: A functor without a direct structure body is not supported yet.
  [1]

  $ caravan --shh fresh_variant_fail.ml
  [Error] File "fresh_variant_fail.ml", line 10, columns 2-25:
  10 |   type t = Wrap of Cell.t
         ^^^^^^^^^^^^^^^^^^^^^^^
  Unsupported Error: A fresh datatype in a functor body is not supported yet.
  [1]

  $ caravan --shh fresh_record_fail.ml
  [Error] File "fresh_record_fail.ml", line 10, columns 2-28:
  10 |   type t = { cell : Cell.t }
         ^^^^^^^^^^^^^^^^^^^^^^^^^^
  Unsupported Error: A fresh datatype in a functor body is not supported yet.
  [1]

  $ caravan --shh hidden_parameter_fail.ml
  [Error] File "hidden_parameter_fail.ml", line 16, columns 13-24:
  16 | let read x = Client.Cell.read x
                    ^^^^^^^^^^^
  Type Error: Unbound module Client.Cell.
  [1]

  $ caravan --shh unused_missing_resource_fail.ml
  [Error] File "unused_missing_resource_fail.ml", line 18, columns 16-35:
  18 | module Client = Make (Actual.First)
                       ^^^^^^^^^^^^^^^^^^^
  Type Error: The actual module does not declare resource missing.
  [1]

  $ caravan --shh abstract_arithmetic_fail.ml
  [Error] File "abstract_arithmetic_fail.ml", line 17, columns 43-44:
  17 |   (*@ result = identity x ensures result = x + 1 *)
                                                  ^
  Type Error: This specification has type Cell.t, but int is required.
  [1]
