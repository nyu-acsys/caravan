  $ caravan --shh arithmetic.ml
  [Error] File "arithmetic.ml", line 16, columns 13-18:
  16 | let incr x = x + 1
                    ^^^^^
  Verification Error: This addition may overflow.
  [Error] File "arithmetic.ml", line 17, columns 14-19:
  17 | let div x y = x / y
                     ^^^^^
  Verification Error: This division may overflow.
  [Error] File "arithmetic.ml", line 17, columns 18-19:
  17 | let div x y = x / y
                         ^
  Verification Error: This divisor may be zero.
  [Error] File "arithmetic.ml", line 22, columns 12-14:
  22 | let neg x = -x
                   ^^
  Verification Error: This negation may overflow.
  [1]
