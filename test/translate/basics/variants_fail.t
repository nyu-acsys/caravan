  $ caravan --shh variants_fail.ml
  [Error] File "variants_fail.ml", line 5, columns 15-41:
  5 | let radius s = match s with Circle r -> r
                     ^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This match may not be exhaustive.
  [Error] File "variants_fail.ml", line 8, columns 52-52:
  8 | let width s = match s with Rect (w, _) -> w | _ -> 0
                                                          ^
  Verification Error: A postcondition may not hold at this return point.
  File "variants_fail.ml", line 10, columns 12-17:
  10 |     ensures w > 0 *)
                   ^^^^^
  Related Location: This assertion may not hold.
  [1]
