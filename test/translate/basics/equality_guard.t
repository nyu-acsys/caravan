Reference equality in contracts requires identity syntax.

  $ caravan --shh equality_ref_fail.ml
  [Error] File "equality_ref_fail.ml", line 2, columns 25-26:
  2 | (*@ claim a b requires a = b *)
                               ^
  Type Error: Structural equality on references is unsupported; use == or != for reference identity.
  [1]

  $ caravan --shh equality_false_proof_ref_fail.ml
  [Error] File "equality_false_proof_ref_fail.ml", line 4, columns 14-15:
  4 |     ensures a = b *)
                    ^
  Type Error: Structural equality on references is unsupported; use == or != for reference identity.
  [1]

Runtime values containing references do not support structural equality.

  $ caravan --shh equality_list_ref_fail.ml
  [Error] File "equality_list_ref_fail.ml", line 2, columns 25-26:
  2 | (*@ claim a b requires a = b *)
                               ^
  Type Error: Structural equality on values containing references is unsupported.
  [1]

  $ caravan --shh equality_option_ref_fail.ml
  [Error] File "equality_option_ref_fail.ml", line 2, columns 25-26:
  2 | (*@ claim a b requires a = b *)
                               ^
  Type Error: Structural equality on values containing references is unsupported.
  [1]

  $ caravan --shh equality_tuple_ref_fail.ml
  [Error] File "equality_tuple_ref_fail.ml", line 2, columns 25-26:
  2 | (*@ claim a b requires a = b *)
                               ^
  Type Error: Structural equality on values containing references is unsupported.
  [1]

  $ caravan --shh equality_record_ref_fail.ml
  [Error] File "equality_record_ref_fail.ml", line 4, columns 25-26:
  4 | (*@ claim a b requires a = b *)
                               ^
  Type Error: Structural equality on values containing references is unsupported.
  [1]

  $ caravan --shh equality_list_mutable_record_fail.ml
  [Error] File "equality_list_mutable_record_fail.ml", line 4, columns 25-26:
  4 | (*@ claim a b requires a = b *)
                               ^
  Type Error: Structural equality on values containing references is unsupported.
  [1]

  $ caravan --shh equality_variant_mutable_record_fail.ml
  [Error] File "equality_variant_mutable_record_fail.ml", line 5, columns 25-26:
  5 | (*@ claim a b requires a = b *)
                               ^
  Type Error: Structural equality on values containing references is unsupported.
  [1]

  $ caravan --shh equality_constructor_ref_fail.ml
  [Error] File "equality_constructor_ref_fail.ml", line 2, columns 30-31:
  2 | (*@ claim a b requires Some a = Some b *)
                                    ^
  Type Error: Structural equality on values containing references is unsupported.
  [1]

  $ caravan --shh equality_projection_ref_fail.ml
  [Error] File "equality_projection_ref_fail.ml", line 4, columns 31-32:
  4 | (*@ claim a b requires a.value = b.value *)
                                     ^
  Type Error: Structural equality on references is unsupported; use == or != for reference identity.
  [1]

  $ caravan --shh equality_if_ref_fail.ml
  [Error] File "equality_if_ref_fail.ml", line 2, columns 56-57:
  2 | (*@ claim choose a b requires (if choose then a else b) = a *)
                                                              ^
  Type Error: Structural equality on references is unsupported; use == or != for reference identity.
  [1]

  $ caravan --shh equality_match_ref_fail.ml
  [Error] File "equality_match_ref_fail.ml", line 2, columns 73-74:
  2 | (*@ claim choose a b requires (match choose with true -> a | false -> b) = a *)
                                                                               ^
  Type Error: Structural equality on references is unsupported; use == or != for reference identity.
  [1]

  $ caravan --shh equality_match_shadow_ref_fail.ml
  [Error] File "equality_match_shadow_ref_fail.proof", line 4, columns 34-35:
  4 |   | Some left, Some right -> left = right
                                        ^
  Type Error: Structural equality on references is unsupported; use == or != for reference identity.
  [1]

  $ caravan --shh equality_runtime_ref_fail.ml
  [Error] File "equality_runtime_ref_fail.ml", line 1, columns 40-45:
  1 | let claim (a : int ref) (b : int ref) = a = b
                                              ^^^^^
  Type Error: Structural equality on values containing references is unsupported.
  [1]

  $ caravan --shh equality_runtime_nested_ref_fail.ml
  [Error] File "equality_runtime_nested_ref_fail.ml", line 1, columns 50-55:
  1 | let claim (a : int ref list) (b : int ref list) = a = b
                                                        ^^^^^
  Type Error: Structural equality on values containing references is unsupported.
  [1]

Boxed physical equality cannot be encoded exactly in specifications.

  $ caravan --shh equality_boxed_physical_fail.ml
  [Error] File "equality_boxed_physical_fail.ml", line 2, columns 25-27:
  2 | (*@ claim a b requires a == b *)
                               ^^
  Type Error: Physical equality on boxed values is unsupported in specifications.
  [1]

  $ caravan --shh equality_math_physical_fail.ml
  [Error] File "equality_math_physical_fail.proof", line 2, columns 14-16:
  2 |   requires (a == b) = ()
                    ^^
  Type Error: Physical equality on logical values is unsupported; use = or <>.
  [1]

The fresh-reference false proof and pure-function path are rejected too.

  $ caravan --shh equality_runtime_fresh_ref_fail.ml
  [Error] File "equality_runtime_fresh_ref_fail.ml", line 4, columns 2-14:
  4 |   left = right
        ^^^^^^^^^^^^
  Type Error: Structural equality on values containing references is unsupported.
  [1]

  $ caravan --shh equality_pure_ref_fail.ml
  [Error] File "equality_pure_ref_fail.ml", line 1, columns 54-66:
  1 | let compare_refs (left : int ref) (right : int ref) = left = right
                                                            ^^^^^^^^^^^^
  Type Error: Structural equality on values containing references is unsupported.
  [1]

Identity, scalar and nullary constructor comparisons remain available.

  $ caravan --shh equality_safe.ml
  Verification successful.

Logical collections with reference elements retain mathematical equality.

  $ caravan --shh equality_math.ml
  Verification successful.

Logical equality compares structure and reference identity without reading contents.

  $ caravan --shh equality_logical.ml
  Verification successful.

Its operands retain their source types before references are erased.

  $ caravan --shh equality_logical_type_fail.ml
  [Error] File "equality_logical_type_fail.proof", line 2, columns 16-19:
  2 |   ensures (left === right) = ()
                      ^^^
  Type Error: Logical equality requires operands of the same OCaml type.
  [1]
