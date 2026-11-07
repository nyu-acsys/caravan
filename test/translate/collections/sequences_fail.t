  $ caravan --shh sequences_fail.ml
  [Error] File "sequences_fail.ml", line 3, columns 20-20:
  3 | let id (n : int) = n
                          ^
  Verification Error: A postcondition may not hold at this return point.
  File "sequences_fail.ml", line 5, columns 37-49:
  5 |     ensures forall s : int sequence. length s > 0
                                           ^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
