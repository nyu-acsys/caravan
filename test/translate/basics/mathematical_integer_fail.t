Mathematical integers cannot be assumed to satisfy machine bounds.

  $ caravan --shh mathematical_integer_bounded_fail.ml
  [Error] File "mathematical_integer_bounded_fail.ml", line 1, columns 19-19:
  1 | let invalid () = ()
                         ^
  Verification Error: A postcondition may not hold at this return point.
  File "mathematical_integer_bounded_fail.ml", line 2, columns 47-63:
  2 | (*@ invalid () ensures forall value : integer. value <= max_int *)
                                                     ^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

The mathematical type is unavailable in executable OCaml.

  $ caravan --shh mathematical_integer_runtime_fail.ml
  [Error] File "mathematical_integer_runtime_fail.ml", line 1, columns 21-28:
  1 | let invalid (value : integer) = value
                           ^^^^^^^
  Type Error: Unbound type constructor integer.
  [1]
