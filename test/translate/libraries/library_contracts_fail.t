  $ caravan --shh library_contracts_fail.ml
  [Error] File "library_contracts_fail.ml", line 5, columns 13-20:
  5 |   Cell.set c (x + 1);
                   ^^^^^^^
  Verification Error: This addition may overflow.
  [Error] File "library_contracts_fail.ml", line 6, columns 3-3:
  6 |   x
         ^
  Verification Error: A postcondition may not hold at this return point.
  File "library_contracts_fail.ml", line 9, columns 12-26:
  9 |     ensures Cell.holds c r *)
                  ^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]
