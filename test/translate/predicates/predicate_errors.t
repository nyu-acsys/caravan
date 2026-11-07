A ghost statement uses a predicate, whose parameters have OCaml types; each file has
its own run.

  $ caravan --shh predicate_error_1.ml
  [Error] File "predicate_error_1.ml", line 6, columns 11-20:
  6 | (*@ unfold valid c n *)
                 ^^^^^^^^^
  Type Error: Expected a predicate applied to its arguments.
  [1]
  $ caravan --shh predicate_error_2.ml
  [Error] File "predicate_error_2.ml", line 3, columns 39-42:
  3 | (*@ predicate valid (c : counter) (n : nat) = own c.count n *)
                                             ^^^
  Type Error: Unbound type constructor nat.
  [1]
