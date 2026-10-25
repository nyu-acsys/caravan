  $ caravan --shh private_member_fail.ml
  [Error] File "private_member_fail.ml", line 8, columns 17-38:
  8 | let call value = Hidden.private_helper value
                       ^^^^^^^^^^^^^^^^^^^^^
  Type Error: Unbound value Hidden.private_helper.
  [1]

  $ caravan --shh private_body_fail.ml
  [Error] File "private_body_fail.ml", line 5, columns 42-42:
  5 |   let private_helper (value : int) = value
                                                ^
  Verification Error: A postcondition may not hold at this return point.
  File "private_body_fail.ml", line 6, columns 44-59:
  6 |   (*@ result = private_helper value ensures result <> value *)
                                                  ^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ caravan --shh abstract_implementation_fail.ml
  [Error] File "abstract_implementation_fail.ml", line 11, columns 37-42:
  11 | let increment (value : Abstract.t) = value + 1
                                            ^^^^^
  Type Error: The value value has type Abstract.t but an expression was expected of type
    int.
  [1]

  $ caravan --shh abstract_spec_fail.ml
  [Error] File "abstract_spec_fail.ml", line 12, columns 33-39:
  12 | (*@ result = fresh value ensures result + 1 = value *)
                                        ^^^^^^
  Type Error: This specification has type Abstract.t, but int is required.
  [1]

  $ caravan --shh signature_contract_fail.ml
  [Error] File "signature_contract_fail.ml", line 5, columns 36-36:
  5 |   let identity (value : int) = value
                                          ^
  Verification Error: A postcondition may not hold at this return point.
  File "signature_contract_fail.ml", line 3, columns 38-52:
  3 |   (*@ result = identity value ensures result > value *)
                                            ^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ caravan --shh distinct_abstract_types_fail.ml
  [Error] File "distinct_abstract_types_fail.ml", line 22, columns 27-44:
  22 | let mix value = Right.read (Left.make value)
                                  ^^^^^^^^^^^^^^^^^
  Type Error: This expression has type Left.t but an expression was expected of type
    Right.t.
  [1]

  $ caravan --shh final_contract_fail.ml
  [Error] File "final_contract_fail.ml", line 3, columns 38-38:
  3 |     let identity (value : int) = value
                                            ^
  Verification Error: A postcondition may not hold at this return point.
  File "final_contract_fail.ml", line 4, columns 40-55:
  4 |     (*@ result = identity value ensures result <> value *)
                                              ^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ caravan --shh functor_fail.ml
  [Error] File "functor_fail.ml", line 1, column 12 to line 6, column 3:
  1 | module Make (Argument : sig
                  ^^^^^^^^^^^^^^^
  Unsupported Error: A functor is not supported yet.
  [1]

  $ caravan --shh include_fail.ml
  [Error] File "include_fail.ml", line 6, columns 2-18:
  6 |   include Original
        ^^^^^^^^^^^^^^^^
  Unsupported Error: An include declaration is not supported yet.
  [1]

  $ caravan --shh open_fail.ml
  [Error] File "open_fail.ml", line 6, columns 2-15:
  6 |   open Original
        ^^^^^^^^^^^^^
  Unsupported Error: An open declaration is not supported yet.
  [1]

  $ caravan --shh effectful_initialization_fail.ml
  [Error] File "effectful_initialization_fail.ml", line 2, columns 2-23:
  2 |   let () = assert false
        ^^^^^^^^^^^^^^^^^^^^^
  Unsupported Error: This definition is not supported yet.
  [1]

  $ caravan --shh abstract_argument_spec_fail.ml
  [Error] File "abstract_argument_spec_fail.ml", line 12, columns 36-41:
  12 | (*@ result = identity value ensures value + 1 = result *)
                                           ^^^^^
  Type Error: This specification has type Abstract.t, but int is required.
  [1]

  $ caravan --shh sealed_contract_fail.ml
  [Error] File "sealed_contract_fail.ml", line 4, columns 2-36:
  4 |   let identity (value : int) = value
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: An exported module member's contract must be declared in its signature.
  [1]

  $ caravan --shh sealed_pure_fail.ml
  [Error] File "sealed_pure_fail.ml", line 8, columns 31-50:
  8 | (*@ result = client () ensures Sealed.value () = 7 *)
                                     ^^^^^^^^^^^^^^^^^^^
  Unsupported Error: A specification call through a constrained module signature is not supported yet.
  [1]

  $ caravan --shh nested_predicate_fail.ml
  [Error] File "nested_predicate_fail.ml", line 4, columns 2-36:
  4 |   (*@ predicate holds (value : t) *)
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Unsupported Error: A predicate declaration in a nested module is not supported yet.
  [1]

  $ caravan --shh signature_predicate_fail.ml
  [Error] File "signature_predicate_fail.ml", line 1, column 19 to line 7, column 3:
  1 | module Container : sig
                         ^^^
  Unsupported Error: A resource declaration on an inline module structure is not supported yet.
  [1]

  $ caravan --shh orphan_contract_fail.ml
  [Error] File "orphan_contract_fail.ml", line 5, columns 0-53:
  5 | (*@ result = identity value ensures result = value *)
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: This contract is outside a function declaration.
  [1]

  $ caravan --shh abstract_ownership_fail.ml
  [Error] File "abstract_ownership_fail.ml", line 12, columns 30-35:
  12 | (*@ client value requires own value 0 *)
                                     ^^^^^
  Type Error: Ownership of an abstract module type must be exposed through a predicate.
  [1]

  $ caravan --shh signature_helper_scope_fail.ml
  [Error] File "signature_helper_scope_fail.ml", line 4, columns 38-44:
  4 |   (*@ result = identity value ensures helper value *)
                                            ^^^^^^
  Unsupported Error: A signature contract referring to another OCaml value is not supported yet.
  [1]

  $ caravan --shh signature_type_scope_fail.ml
  [Error] File "signature_type_scope_fail.ml", line 7, columns 45-52:
  7 |   (*@ result = identity value ensures forall witness : t. witness = witness *)
                                                   ^^^^^^^
  Unsupported Error: A signature contract whose names have a different implementation scope is not supported yet.
  [1]

  $ caravan --shh private_constructor_spec_fail.ml
  [Error] File "private_constructor_spec_fail.ml", line 5, columns 40-46:
  5 |   (*@ result = make () ensures result = Hidden *)
                                              ^^^^^^
  Type Error: A specification cannot construct a value of a private type.
  [1]

  $ caravan --shh abstract_signature_ownership_fail.ml
  [Error] File "abstract_signature_ownership_fail.ml", line 5, columns 42-46:
  5 |   (*@ result = identity cell requires own cell 0 ensures own result 0 *)
                                                ^^^^
  Type Error: Ownership of an abstract module type must be exposed through a predicate.
  [1]

  $ caravan --shh abstract_pattern_projection_fail.ml
  [Error] File "abstract_pattern_projection_fail.ml", line 13, columns 45-51:
  13 |     ensures match result with Some hidden -> hidden + 1 = value | None -> true *)
                                                    ^^^^^^
  Type Error: This specification has type Sealed.t, but int is required.
  [1]

  $ caravan --shh abstract_collection_spec_fail.ml
  [Error] File "abstract_collection_spec_fail.ml", line 5, columns 46-51:
  5 |   (*@ result = identity value requires length value = 0 ensures result = value *)
                                                    ^^^^^
  Type Error: This collection operation requires a visible collection type.
  [1]
