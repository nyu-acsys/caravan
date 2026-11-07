  $ caravan --shh fail.ml
  [Error] File "fail.ml", line 3, columns 19-19:
  3 | let wrong x = x + 1
                         ^
  Verification Error: A postcondition may not hold at this return point.
  File "fail.ml", line 6, columns 12-17:
  6 |     ensures r = x *)
                  ^^^^^
  Related Location: This assertion may not hold.
  [Error] File "fail.ml", line 13, columns 15-21:
  13 | let caller x = pred x
                      ^^^^^^
  Verification Error: A precondition may not hold for this call.
  File "fail.ml", line 10, columns 13-18:
  10 |     requires n > 0
                    ^^^^^
  Related Location: This assertion may not hold.
  [Error] File "fail.ml", line 14, columns 25-32:
  14 | let unchecked x = assert (x > 0)
                                ^^^^^^^
  Verification Error: This assertion may be violated.
  [1]
