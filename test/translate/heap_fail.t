  $ caravan --shh heap_fail.ml
  [Error] File "heap_fail.ml", line 5, columns 12-19:
  5 | let get c = c.count
                  ^^^^^^^
  Verification Error: Could not assert sufficient permissions to access this field.
  [Error] File "heap_fail.ml", line 8, columns 26-26:
  8 | let reset c = c.count <- 1
                                ^
  Verification Error: A postcondition may not hold at this return point.
  File "heap_fail.ml", line 11, columns 12-25:
  11 |     ensures own c.count 0 *)
                   ^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
