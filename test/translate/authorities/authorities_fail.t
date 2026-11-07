Authorities cannot issue unknown facts or erase facts whose fragments might be
held by another thread.

  $ caravan --shh authorities_fail.ml
  [Error] File "authorities_fail.proof", line 13, column 2 to line 15, column 79:
  13 |   Ghost.fpu (Ghost.at facts cell)
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This update may not be frame-preserving.
  [Error] File "authorities_fail.proof", line 21, column 2 to line 23, column 45:
  21 |   Ghost.fpu (Ghost.at facts cell)
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This update may not be frame-preserving.
  [Error] File "authorities_fail.proof", line 26, column 2 to line 28, column 45:
  26 |   Ghost.fpu (Ghost.at facts cell)
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This update may not be frame-preserving.
  File "authorities_fail.proof", line 26, column 2 to line 28, column 45:
  26 |   Ghost.fpu (Ghost.at facts cell)
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
