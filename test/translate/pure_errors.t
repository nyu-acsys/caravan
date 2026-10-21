Functions that contracts use must be pure, and variants are not supported yet; each file
has its own run.

  $ caravan --shh pure_error_1.ml
  [Error] File "pure_error_1.ml", line 2, column 2 to line 3, column 3:
  2 |   assert (x > 0);
        ^^^^^^^^^^^^^^^
  Unsupported Error: This expression in a function that contracts use, which must be pure, is not supported yet.
  [1]
  $ caravan --shh pure_error_2.ml
  [Error] File "pure_error_2.ml", line 1, columns 27-51:
  1 | let first (l : int list) = match l with x :: _ -> x
                                 ^^^^^^^^^^^^^^^^^^^^^^^^
  Unsupported Error: A match that may not be exhaustive in a function that contracts use, which must be pure, is not supported yet.
  [1]
  $ caravan --shh pure_error_3.ml
  [Error] File "pure_error_3.ml", line 3, columns 12-13:
  3 |     variant n *)
                  ^
  Unsupported Error: A variant is not supported yet.
  [1]
