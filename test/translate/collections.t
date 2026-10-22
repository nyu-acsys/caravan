  $ caravan --shh collections.ml
  Verification successful.

  $ caravan --shh collections_fail.ml
  [Error] File "collections_fail.proof", line 1, columns 13-13:
  1 | lemma removed (s : int finset) (x : int)
                   ^
  Verification Error: A postcondition may not hold at this return point.
  File "collections_fail.proof", line 2, columns 11-60:
  2 |   ensures (Finset.mem x (Finset.diff s (Finset.singleton x))) = ()
                 ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

New logical types preserve existing source type names. Proof declarations cannot
shadow source types or constructors.

  $ caravan --shh proof_collection_shadow.ml
  Verification successful.

  $ caravan --shh proof_type_shadow.ml
  [Error] File "proof_type_shadow.proof", line 1, columns 5-9:
  1 | type item = Other of int
           ^^^^
  Type Error: The proof type item is already declared.
  [1]

  $ caravan --shh proof_constructor_shadow.ml
  [Error] File "proof_constructor_shadow.proof", line 1, columns 18-22:
  1 | type ghost_item = Item of int
                        ^^^^
  Type Error: The proof constructor Item is already declared.
  [1]

A declared library predicate takes precedence over a logical collection operation.

  $ caravan --shh -I include_dirs collections_module_shadow.ml
  Verification successful.
