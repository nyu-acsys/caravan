  $ caravan --shh predicates_fail.ml
  [Error] File "predicates_fail.ml", line 7, columns 27-27:
  7 | let make () = { count = 0 }
                                 ^
  Verification Error: A postcondition may not hold at this return point.
  File "predicates_fail.ml", line 9, columns 12-21:
  9 |     ensures valid c 0 *)
                  ^^^^^^^^^
  Related Location: This predicate may not hold.
  [Error] File "predicates_fail.ml", line 11, columns 14-26:
  11 | let set c v = c.count <- v
                     ^^^^^^^^^^^^
  Verification Error: Could not assert sufficient permissions to assign this field.
  [Error] File "predicates_fail.ml", line 15, columns 9-18:
  15 | (*@ fold valid c v *)
                ^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  File "predicates_fail.ml", line 5, columns 68-77:
  5 | (*@ predicate valid (c : counter) (n : int) = own c.count n && 0 <= n <= 1000 *)
                                                                          ^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
