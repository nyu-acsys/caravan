  $ caravan --shh lock_fail.ml
  [Error] File "lock_fail.ml", line 9, columns 16-33:
  9 | let release l = Atomic.set l true
                      ^^^^^^^^^^^^^^^^^
  Verification Error: The atomic postcondition may not hold after this step, which linearizes the function.
  File "lock_fail.mli", line 19, columns 19-34:
  19 |     atomic ensures is_lock l false *)
                          ^^^^^^^^^^^^^^^
  Related Location: This part of the atomic postcondition may not hold.
  [1]
