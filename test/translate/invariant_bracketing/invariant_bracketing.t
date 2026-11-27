A step at a primitive access opens the invariants of the opens clause around its
proof: the unfolded state is named current, and an explicit fold replaces the
unchanged one.

  $ caravan --shh counter.ml
  Verification successful.

A step at a call to a checked procedure opens nothing.

  $ sed 's/(fun invoke -> let result = invoke () in result)/(fun invoke -> let result = invoke () in assert (0 <= current.value); result)/' counter.mlp > call_fail.mlp
  $ cp counter.ml call_fail.ml
  $ caravan --shh --only get_twice call_fail.ml
  [Error] File "call_fail.mlp", line 31, columns 84-91:
  31 |   at ((get c)[@occurrence 1]) (fun invoke -> let result = invoke () in assert (0 <= current.value); result)
                                                                                           ^^^^^^^
  Type Error: Unbound name current.
  [1]

A namespace in the opens clause is no instance to open.

  $ grep -v 'unfold counter c;\|    fold counter c;' counter.mlp > namespace_fail.mlp
  $ cp counter.ml namespace_fail.ml
  $ caravan --shh --only get_namespace namespace_fail.ml
  [Error] File "namespace_fail.ml", line 5, columns 39-51:
  5 | let get_namespace (c : int Atomic.t) = Atomic.get c
                                             ^^^^^^^^^^^^
  Verification Error: Could not assert sufficient permissions to access this field.
  [Error] File "namespace_fail.ml", line 5, columns 51-51:
  5 | let get_namespace (c : int Atomic.t) = Atomic.get c
                                                         ^
  Verification Error: A postcondition may not hold at this return point.
  File "namespace_fail.ml", line 5, columns 0-51:
  5 | let get_namespace (c : int Atomic.t) = Atomic.get c
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  File "namespace_fail.mlp", line 36, columns 24-35:
  36 |   ensures (counter c && 0 <= result) =
                               ^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
