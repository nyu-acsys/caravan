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

Reads and writes of entries anchor proof scopes, which can lend a fraction of an
invariant's ownership to a read.

  $ caravan --shh anchors.ml
  Verification successful.

  $ caravan --shh anchors_fail.ml
  [Error] File "anchors_fail.ml", line 1, columns 29-34:
  1 | let read (a : int array) i = a.(i)
                                   ^^^^^
  Verification Error: A precondition may not hold for this call.
  Related Location: This assertion may not hold
  Related Location: This own predicate may not hold
  [1]

An array of mutexes guards a cell of another array per index. An invariant lends a
fraction of the mutexes' cells to each read, and the loop that creates them names the
map from indices to mutexes as its invariant's witness.

  $ caravan --shh --smt-timeout=30000 mutexes.ml
  Verification successful.

Entries guarded by their mutexes cannot be accessed without them.

  $ caravan --shh mutexes_fail.ml
  [Error] File "mutexes_fail.ml", line 3, columns 31-43:
  3 | let incr s i = s.counts.(i) <- s.counts.(i) + 1
                                     ^^^^^^^^^^^^
  Verification Error: A precondition may not hold for this call.
  Related Location: This assertion may not hold
  Related Location: This own predicate may not hold
  [1]
