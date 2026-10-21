  $ caravan --shh atomic_contracts_fail.ml
  [Error] File "atomic_contracts_fail.ml", line 11, columns 19-34:
  11 |     atomic ensures is_lock l false *)
                          ^^^^^^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  File "atomic_contracts_fail.ml", line 11, columns 19-34:
  11 |     atomic ensures is_lock l false *)
                          ^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [Error] File "atomic_contracts_fail.ml", line 14, columns 27-63:
  14 | let rec acquire l = if not (Atomic.compare_and_set l true true) then acquire l
                                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: An atomic postcondition may not hold at this commit point.
  [Error] File "atomic_contracts_fail.ml", line 14, columns 27-63:
  14 | let rec acquire l = if not (Atomic.compare_and_set l true true) then acquire l
                                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: A postcondition may not hold at this return point.
  File "atomic_contracts_fail.ml", line 17, columns 37-46:
  17 |     atomic ensures is_lock l true && b = false *)
                                            ^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
