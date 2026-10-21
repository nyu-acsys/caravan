Proofs that do not fit their interface; each file has its own run.

  $ caravan --shh proof_error_1.ml
  [Error] File "proof_error_1.proof", line 3, columns 5-10:
  3 | view stack (t : t) = s.items
           ^^^^^
  Type Error: The view stack is not declared in the interface, which gives the type of its value.
  [1]
  $ caravan --shh proof_error_2.ml
  [Error] File "proof_error_2.proof", line 1, columns 28-29:
  1 | invariant is_stack (t : t) (s : state) = own t s.items
                                  ^
  Type Error: The state of an invariant has a type declared in the proof, as type state = { ... }.
  [1]
  $ caravan --shh proof_error_3.ml
  [Error] File "proof_error_3.proof", line 1, columns 10-18:
  1 | predicate is_stack (t : t) = own t []
                ^^^^^^^^
  Type Error: The predicate is_stack is declared [@persistent], so it is defined as an invariant.
  File "proof_error_3.mli", line 2, columns 0-47:
  2 | (*@ predicate is_stack (t : t) [@persistent] *)
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: Its declaration.
  [1]
  $ caravan --shh proof_error_4.ml
  [Error] File "proof_error_4.proof", line 2, columns 47-57:
  2 | invariant is_stack (t : t) (s : state) = own t s.contents
                                                     ^^^^^^^^^^
  Type Error: The state s has no field contents.
  [1]
