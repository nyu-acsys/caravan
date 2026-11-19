A cut proves its assertion and verifies the rest from it and the values of
variables alone, in an annotation or in a proof outline. In an atomic step, the
invariants the step opened are closed before the cut. A value read before the cut
keeps its value but not its range, which the cut restates.

  $ caravan --shh refs.ml
  Verification successful.
  $ caravan --shh counter.ml
  Verification successful.

What the cut leaves out is gone: here, the ownership of s.

  $ sed '0,/  r := 3;/s//  s := 3;/' refs.ml > left_behind.ml
  $ cp refs.mli left_behind.mli
  $ caravan --shh --only keep left_behind.ml
  [Error] File "left_behind.ml", line 5, columns 2-8:
  5 |   s := 3;
        ^^^^^^
  Verification Error: A precondition may not hold for this call.
  Related Location: This own predicate may not hold
  [1]

So are the facts about the heap: x keeps its value, but no longer equals a.

  $ sed 's/(\*@ cut own r.contents x && x = a \*)/(*@ cut own r.contents x *)/' refs.ml > forgotten.ml
  $ cp refs.mli forgotten.mli
  $ caravan --shh --only read_restated forgotten.ml
  [Error] File "forgotten.ml", line 12, columns 3-3:
  12 |   x
          ^
  Verification Error: A postcondition may not hold at this return point.
  File "forgotten.mli", line 9, columns 32-42:
  9 |     ensures own r.contents 3 && result = a *)
                                      ^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
