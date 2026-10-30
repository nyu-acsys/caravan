  $ caravan --shh atomics_fail.ml
  [Error] File "atomics_fail.ml", line 4, columns 37-37:
  4 |   Atomic.compare_and_set a l (x :: l)
                                           ^
  Verification Error: A postcondition may not hold at this return point.
  File "atomics_fail.ml", line 7, columns 12-26:
  7 |     ensures own a (x :: l) && r *)
                  ^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [Error] File "atomics_fail.ml", line 9, columns 34-34:
  9 | let same (a : int list) b = a == b
                                        ^
  Verification Error: A postcondition may not hold at this return point.
  File "atomics_fail.ml", line 12, columns 12-13:
  12 |     ensures r *)
                   ^
  Related Location: This assertion may not hold.
  [Error] File "atomics_fail.ml", line 14, columns 33-47:
  14 | let unowned (a : int Atomic.t) = Atomic.set a 1
                                        ^^^^^^^^^^^^^^
  Verification Error: Could not assert sufficient permissions to assign this field.
  [Error] File "atomics_fail.ml", line 15, columns 30-30:
  15 | let overflow a = Atomic.incr a
                                     ^
  Verification Error: A postcondition may not hold at this return point.
  File "atomics_fail.ml", line 18, columns 12-31:
  18 |     ensures own a (max_int + 1) *)
                   ^^^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
