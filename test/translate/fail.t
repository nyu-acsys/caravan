  $ caravan --shh fail.ml
  [Error] File "fail.ml", line 3, columns 19-19:
  3 | let wrong x = x + 1
                         ^
  Verification Error: A postcondition may not hold at this return point.
  File "fail.ml", line 5, columns 12-17:
  5 |     ensures r = x *)
                  ^^^^^
  Related Location: This assertion may not hold.
  [Error] File "fail.ml", line 12, columns 15-21:
  12 | let caller x = pred x
                      ^^^^^^
  Verification Error: A precondition may not hold for this call.
  File "fail.ml", line 9, columns 13-18:
  9 |     requires n > 0
                   ^^^^^
  Related Location: This assertion may not hold.
  [Error] File "fail.ml", line 13, columns 25-32:
  13 | let unchecked x = assert (x > 0)
                                ^^^^^^^
  Verification Error: This assertion may be violated.
  [1]
