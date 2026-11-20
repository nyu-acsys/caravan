Arrays are ordinary cells, one per index, owned through Array.cell; their lengths are
fixed, and indices and lengths out of bounds are errors to prove absent.

  $ caravan --shh arrays.ml
  Verification successful.

  $ caravan --shh failures.ml
  [Error] File "failures.ml", line 3, columns 2-7:
  3 |   a.(3)
        ^^^^^
  Verification Error: This index may be out of the array's bounds.
  [Error] File "failures.ml", line 5, columns 18-38:
  5 | let negative () = Array.make (-1) true
                        ^^^^^^^^^^^^^^^^^^^^
  Verification Error: This array length may be negative or too large.
  [Error] File "failures.ml", line 6, columns 30-40:
  6 | let unowned (a : int array) = a.(0) <- 1
                                    ^^^^^^^^^^
  Verification Error: A precondition may not hold for this call.
  Related Location: This own predicate may not hold
  [1]
