  $ caravan --shh loops_fail.ml
  [Error] File "loops_fail.ml", line 6, column 2 to line 9, column 6:
  6 |   for _ = 1 to n do
        ^^^^^^^^^^^^^^^^^
  Verification Error: This loop invariant may not hold upon loop entry.
  File "loops_fail.ml", line 7, columns 18-34:
  7 |     (*@ invariant own s.contents v && v = 1 *)
                        ^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  File "loops_fail.ml", line 7, columns 38-43:
  7 |     (*@ invariant own s.contents v && v = 1 *)
                                            ^^^^^
  Related Location: This assertion may not hold.
  [Error] File "loops_fail.ml", line 15, column 2 to line 18, column 6:
  15 |   while !c < n do
         ^^^^^^^^^^^^^^^
  Verification Error: This loop invariant may not be maintained.
  File "loops_fail.ml", line 16, columns 38-44:
  16 |     (*@ invariant own c.contents k && k <= 0 *)
                                             ^^^^^^
  Related Location: This assertion may not hold.
  [Error] File "loops_fail.ml", line 28, columns 4-4:
  28 |   !c
           ^
  Verification Error: A postcondition may not hold at this return point.
  File "loops_fail.ml", line 31, columns 12-17:
  31 |     ensures r = n *)
                   ^^^^^
  Related Location: This assertion may not hold.
  [1]
