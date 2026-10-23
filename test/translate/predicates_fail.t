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
  Verification Error: A precondition may not hold for this call.
  Related Location: This own predicate may not hold
  [1]
