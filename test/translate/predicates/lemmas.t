Checked lemmas can prove list append associativity by recursion, return ghost results,
and be applied from an OCaml ghost annotation.

  $ caravan --shh lemmas.ml
  Verification successful.

Unreachable branches can use assert false at any result type; its assertion is
still checked, and other assertions return unit.

  $ caravan --shh lemmas_false_result.ml
  [Error] File "lemmas_false_result.proof", line 1, columns 51-56:
  1 | lemma false_result returns (result : int) = assert false
                                                         ^^^^^
  Verification Error: This assertion may be violated.
  [1]

  $ caravan --shh lemmas_assert_unit.ml
  [Error] File "lemmas_assert_unit.proof", line 1, columns 44-55:
  1 | lemma not_a_result returns (result : int) = assert true
                                                  ^^^^^^^^^^^
  Type Error: This proof expression returns unit.
  [1]

Existential witnesses can be named while unfolding and supplied while folding an
owned predicate.

  $ caravan --shh lemmas_witness.ml
  Verification successful.

Unfolding into a witness record binds all existentials as its fields, which a fold
takes as they are or updated, also where a branch has none.

  $ caravan --shh witness_records.ml
  Verification successful.

  $ caravan --shh witness_records_fail.ml
  [Error] File "witness_records_fail.proof", line 7, columns 7-13:
  7 |   fold held b { w with c = w.n - 1 }
             ^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  File "witness_records_fail.proof", line 1, columns 73-79:
  1 | predicate held (b : box) = exists n : int, c : integer. own b.value n && n <= c
                                                                               ^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ caravan --shh witness_records_unknown.ml
  [Error] File "witness_records_unknown.proof", line 7, columns 23-28:
  7 |   fold held b { w with count = w.c }
                             ^^^^^
  Type Error: The witness record w has no field count.
  [1]

  $ caravan --shh witness_records_not_record.ml
  [Error] File "witness_records_not_record.proof", line 7, columns 14-30:
  7 |   fold held b { v with c = 0 }
                    ^^^^^^^^^^^^^^^^
  Type Error: Only a witness record can be updated.
  [1]

A record type that no invariant takes as its state is a logical record. An existential
record is one existential per field. Unfolding a predicate whose only existential is a
record binds that record, which a fold takes as its last argument. A fold can also name
some of its fields, leaving the others to Raven.

  $ caravan --shh logical_records.ml
  Verification successful.

  $ caravan --shh logical_records_fail.ml
  [Error] File "logical_records_fail.proof", line 9, columns 7-13:
  9 |   fold held b { s with c = s.n - 1 }
             ^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  File "logical_records_fail.proof", line 3, columns 64-74:
  3 | predicate held (b : box) = exists s : count. own b.value s.n && s.n <= s.c
                                                                      ^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ caravan --shh logical_records_grows.ml
  [Error] File "logical_records_grows.proof", line 1, columns 24-25:
  1 | type count = { n : int; c : integer [@grows] }
                              ^
  Syntax Error: Only the state of an invariant has [@grows] or [@helps] fields.
  [1]

  $ caravan --shh logical_records_named.ml
  [Error] File "logical_records_named.proof", line 8, columns 31-32:
  8 |   let (s, m) = unfold pair b { s; m } in
                                     ^
  Type Error: Unfold into a record to bind the existential record s, as let w = unfold p x.
  [1]

  $ caravan --shh logical_records_field.ml
  [Error] File "logical_records_field.proof", line 4, columns 24-25:
  4 |   ensures (t = { s with d = s.c + 1 }) =
                              ^
  Type Error: This record has no field d.
  [1]

  $ caravan --shh logical_records_type.ml
  [Error] File "logical_records_type.proof", line 9, columns 23-24:
  9 |   fold held b { s with d = 1 }
                             ^
  Type Error: This record expression is expected to have type count
  There is no field d within type count.
  [1]

An inline predicate stands for its body, so it is never folded or unfolded.

  $ caravan --shh inline_predicates.ml
  Verification successful.

  $ caravan --shh inline_predicates_fold.ml
  [Error] File "inline_predicates_fold.proof", line 8, columns 9-16:
  8 |   unfold bounded s
               ^^^^^^^
  Type Error: An inline predicate stands for its body and is never folded or unfolded.
  [1]

An assertion in a proof body is checked.

  $ caravan --shh lemmas_false.ml
  [Error] File "lemmas_false.proof", line 1, columns 28-33:
  1 | lemma false_claim = assert (false)
                                  ^^^^^
  Verification Error: This assertion may be violated.
  [1]

Recursive lemmas need a variant that decreases.

  $ caravan --shh lemmas_no_variant.ml
  [Error] File "lemmas_no_variant.proof", line 1, columns 6-10:
  1 | lemma loop (n : int) = loop n
            ^^^^
  Type Error: A recursive lemma needs a variant.
  [1]

  $ caravan --shh lemmas_non_decreasing.ml
  [Error] File "lemmas_non_decreasing.proof", line 1, columns 30-31:
  1 | lemma loop (n : int) variant (n) = loop n
                                    ^
  Verification Error: This decreases clause's termination measure may not decrease on this recursive call.
  [1]

Calls to undeclared lemmas are rejected in ghost annotations.

  $ caravan --shh lemmas_unknown.ml
  [Error] File "lemmas_unknown.ml", line 2, columns 12-19:
  2 |   (*@ lemma missing 0 *)
                  ^^^^^^^
  Type Error: Unknown lemma missing.
  [1]

Mutual recursion also needs a variant; a proof cannot call a runtime procedure.

  $ caravan --shh lemmas_mutual.ml
  [Error] File "lemmas_mutual.proof", line 1, columns 6-11:
  1 | lemma first (n : int) ensures (false) = second n
            ^^^^^
  Type Error: A recursive lemma needs a variant.
  [1]

  $ caravan --shh lemmas_runtime_call.ml
  [Error] File "lemmas_runtime_call.proof", line 1, columns 16-20:
  1 | lemma ignored = idle ()
                      ^^^^
  Type Error: Unknown lemma idle.
  [1]

A type mismatch in an explicit proof is reported as a user type error.

  $ caravan --shh lemmas_type_error.ml
  [Error] File "lemmas_type_error.proof", line 1, columns 30-34:
  1 | lemma wrong = let (n : int) = true in ()
                                    ^^^^
  Type Error: This expression should not be a boolean literal, the expected type is
  int.
  [1]

A binding inside a nested block does not escape its lexical scope.

  $ caravan --shh lemmas_scope_leak.ml
  [Error] File "lemmas_scope_leak.proof", line 3, columns 2-8:
  3 |   hidden
        ^^^^^^
  Type Error: Unknown lemma hidden.
  [1]

A match expression in a lemma must handle every reachable case.

  $ caravan --shh lemmas_partial_match.ml
  [Error] File "lemmas_partial_match.proof", line 2, columns 2-34:
  2 |   match x with Some value -> value
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This match may not be exhaustive.
  [1]

A recursive call in a let binding still requires a variant.

  $ caravan --shh lemmas_rhs_recursion.ml
  [Error] File "lemmas_rhs_recursion.proof", line 1, columns 6-10:
  1 | lemma loop (n : int) =
            ^^^^
  Type Error: A recursive lemma needs a variant.
  [1]

Unfold witnesses determine binding types; unknown or ambiguous witness names and
incompatible explicit annotations are rejected.

  $ caravan --shh lemmas_witness_unknown.ml
  [Error] File "lemmas_witness_unknown.proof", line 5, columns 29-36:
  5 |   let value = unfold held b {missing} in ()
                                   ^^^^^^^
  Type Error: Predicate held has no existential named missing.
  [1]

  $ caravan --shh lemmas_witness_ambiguous.ml
  [Error] File "lemmas_witness_ambiguous.proof", line 6, columns 29-30:
  6 |   let value = unfold held b {n} in ()
                                   ^
  Type Error: Existential name n is ambiguous in predicate held.
  [1]

  $ caravan --shh lemmas_witness_type_error.ml
  [Error] File "lemmas_witness_type_error.proof", line 5, columns 23-40:
  5 |   let (value : bool) = unfold held b {n} in ()
                             ^^^^^^^^^^^^^^^^^
  Type Error: Expected an expression of type
    Bool
  but found an expression of type
    Int.
  [1]
