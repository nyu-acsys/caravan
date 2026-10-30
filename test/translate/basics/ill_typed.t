  $ caravan --shh ill_typed.ml
  [Error] File "ill_typed.ml", line 1, columns 22-26:
  1 | let f (x : int) = x + true
                            ^^^^
  Type Error: This expression should not be a boolean literal, the expected type is
  int.
  [1]
