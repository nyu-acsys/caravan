Access proofs preserve the operation, its result, and its source attachment.

  $ caravan --shh access_changed_result_fail.ml
  [Error] File "access_changed_result_fail.ml", line 2, columns 53-63:
  2 | (*@ Ghost.scope (fun read -> let result = read () in result + 1) *)
                                                           ^^^^^^^^^^
  Type Error: An access proof must return the unchanged result of the attached operation.
  [1]

  $ caravan --shh access_duplicate_read_fail.ml
  [Error] File "access_duplicate_read_fail.ml", line 4, column 8 to line 5, column 14:
  4 |         let duplicate = read () in
              ^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: Bind the attached operation once in an unconditional let.
  [1]

  $ caravan --shh access_conditional_read_fail.ml
  [Error] File "access_conditional_read_fail.ml", line 3, columns 8-58:
  3 |         if true then let result = read () in result else 0) *)
              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: An access proof needs one unconditional let binding of the attached operation.
  [1]

  $ caravan --shh access_missing_read_fail.ml
  [Error] File "access_missing_read_fail.ml", line 2, columns 29-30:
  2 | (*@ Ghost.scope (fun read -> 0) *)
                                   ^
  Type Error: An access proof needs one unconditional let binding of the attached operation.
  [1]

  $ caravan --shh access_escaping_read_fail.ml
  [Error] File "access_escaping_read_fail.ml", line 3, columns 22-26:
  3 |         let escaped = read in
                            ^^^^
  Type Error: Bind the attached operation once in an unconditional let.
  [1]

  $ caravan --shh access_shadowed_result_fail.ml
  [Error] File "access_shadowed_result_fail.ml", line 5, columns 8-14:
  5 |         result) *)
              ^^^^^^
  Type Error: An access proof must return the unchanged result of the attached operation.
  [1]

  $ caravan --shh access_nonatomic_call_fail.ml
  [Error] File "access_nonatomic_call_fail.ml", line 2, columns 0-63:
  2 | (*@ Ghost.scope (fun read -> let result = read () in result) *)
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: Ghost.scope must follow an Atomic access or a checked procedure call.
  [1]

  $ caravan --shh access_existing_value_fail.ml
  [Error] File "access_existing_value_fail.ml", line 4, columns 0-63:
  4 | (*@ Ghost.scope (fun read -> let result = read () in result) *)
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: Ghost.scope must follow an Atomic access or a checked procedure call.
  [1]

  $ caravan --shh access_automatic_fail.ml
  [Error] File "access_automatic_fail.ml", line 2, columns 0-63:
  2 | (*@ Ghost.scope (fun read -> let result = read () in result) *)
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: Ghost.scope requires a manual function proof.
  [1]

  $ caravan --shh access_manual_commit_fail.ml
  [Error] File "access_manual_commit_fail.ml", line 2, columns 0-13:
  2 | (*@ commit *)
      ^^^^^^^^^^^^^
  Type Error: Automatic linearization annotations cannot be used in a manual function proof.
  [1]

  $ caravan --shh access_manual_trusted_fail.ml
  [Error] File "access_manual_trusted_fail.ml", line 2, columns 0-63:
  2 | (*@ Ghost.scope (fun read -> let result = read () in result) *)
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: Ghost.scope cannot be used in a trusted function.
  [1]

  $ caravan --shh access_shadowed_lemma_fail.ml
  [Error] File "access_shadowed_lemma_fail.ml", line 4, columns 4-10:
  4 |     helper ();
          ^^^^^^
  Type Error: A local proof value cannot be called as a lemma.
  [1]
