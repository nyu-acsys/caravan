Ghost fields preserve the owner and nominal resource types, and resource
instances must be declared before use.

  $ caravan --shh authorities_wrong_instance.ml
  [Error] File "authorities_wrong_instance.proof", line 9, columns 38-83:
  9 |   requires (own (Ghost.at facts cell) (Other_auth.auth (Other_facts.set Set.empty))) = ()
                                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: This expression has type Other_auth.t but an expression was expected of type
    Facts_auth.t.
  [1]

  $ caravan --shh authorities_wrong_owner.ml
  [Error] File "authorities_wrong_owner.proof", line 7, columns 33-37:
  7 |   requires (own (Ghost.at facts (cell : node Atomic.t))
                                       ^^^^
  Type Error: The value cell has type int Atomic.t but an expression was expected of type
    node Atomic.t
  Type int is not compatible with type node.
  [1]

  $ caravan --shh authorities_plain_resource.ml
  [Error] File "authorities_plain_resource.proof", line 7, columns 38-39:
  7 |   requires (own (Ghost.at facts cell) 0) = ()
                                            ^
  Type Error: The constant 0 has type int but an expression was expected of type
    Facts_auth.t.
  [1]

  $ caravan --shh authorities_forward.ml
  [Error] File "authorities_forward.proof", line 1, columns 26-31:
  1 | module Facts_auth = Auth (Facts)
                                ^^^^^
  Type Error: The proof module argument is not declared.
  [1]

Pure logical definitions cannot read ownership or assume recursive equations.

  $ caravan --shh authorities_pure_heap.ml
  [Error] File "authorities_pure_heap.proof", line 1, columns 46-49:
  1 | let heap_fact (cell : node Atomic.t) : bool = own cell End
                                                    ^^^
  Type Error: A pure logical function cannot use ownership or predicates.
  [1]

  $ caravan --shh authorities_pure_recursive.ml
  [Error] File "authorities_pure_recursive.proof", line 1, columns 35-43:
  1 | let circular (value : int) : int = circular value
                                         ^^^^^^^^
  Type Error: A logical function can only call earlier logical definitions.
  [1]

Logical definitions and calls retain OCaml reference types and lexical scope.

  $ caravan --shh logical_functions_cast.ml
  [Error] File "logical_functions_cast.proof", line 1, columns 57-61:
  1 | let invalid_cast (cell : bool Atomic.t) : int Atomic.t = cell
                                                               ^^^^
  Type Error: The value cell has type bool Atomic.t but an expression was expected of type
    int Atomic.t
  Type bool is not compatible with type int.
  [1]

  $ caravan --shh logical_functions_argument.ml
  [Error] File "logical_functions_argument.proof", line 4, columns 38-42:
  4 |   let result = identity (if true then cell else cell) in ()
                                            ^^^^
  Type Error: The value cell has type bool Atomic.t but an expression was expected of type
    int Atomic.t
  Type bool is not compatible with type int.
  [1]

  $ caravan --shh logical_functions_shadow.ml
  [Error] File "logical_functions_shadow.proof", line 2, columns 38-46:
  2 | let shadowed (identity : int) : int = identity 0
                                            ^^^^^^^^
  Type Error: This expression has type int
  This is not a function; it cannot be applied..
  [1]

  $ caravan --shh logical_functions_partial.ml
  [Error] File "logical_functions_partial.proof", line 2, columns 2-43:
  2 |   match items with first :: _ :: _ -> first
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: A logical match must be exhaustive.
  [1]
