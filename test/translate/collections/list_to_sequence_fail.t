Sequence builtins reject lists, whose own functions or conversion apply instead.

  $ caravan --shh sequence_builtin_on_list.ml
  [Error] File "sequence_builtin_on_list.ml", line 3, columns 39-40:
  3 | (*@ r = rev_onto xs acc ensures length r = length xs + length acc *)
                                             ^
  Type Error: length applies to sequences; use List.length for lists.
  [1]

  $ caravan --shh sequence_slice_on_list.ml
  [Error] File "sequence_slice_on_list.ml", line 2, columns 31-32:
  2 | (*@ r = keep xs ensures drop 1 r = drop 1 xs *)
                                     ^
  Type Error: drop applies to sequences; convert a list with to_sequence.
  [1]

  $ caravan --shh list_length.ml
  Verification successful.

The conversion only accepts lists.

  $ caravan --shh list_to_sequence_wrong_input.ml
  [Error] File "list_to_sequence_wrong_input.ml", line 2, columns 55-60:
  2 | (*@ result = invalid value ensures length (to_sequence value) = 0 *)
                                                             ^^^^^
  Type Error: The value value has type int but an expression was expected of type 'a list.
  [1]

Reference element types remain distinct before Raven erases them.

  $ caravan --shh list_to_sequence_wrong_refs.ml
  [Error] File "list_to_sequence_wrong_refs.proof", line 4, columns 17-35:
  4 |   fold int_refs (to_sequence [cell])
                       ^^^^^^^^^^^^^^^^^^
  Type Error: This expression has type bool ref sequence
  but an expression was expected of type int ref sequence
  Type bool is not compatible with type int.
  [1]

Conversion preserves list order.

  $ caravan --shh list_to_sequence_wrong_order.ml
  [Error] File "list_to_sequence_wrong_order.ml", line 1, columns 19-19:
  1 | let invalid () = ()
                         ^
  Verification Error: A postcondition may not hold at this return point.
  File "list_to_sequence_wrong_order.ml", line 2, columns 23-50:
  2 | (*@ invalid () ensures to_sequence [1; 2] = [2; 1] *)
                             ^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

The logical conversion is unavailable in executable OCaml.

  $ caravan --shh list_to_sequence_runtime_fail.ml
  [Error] File "list_to_sequence_runtime_fail.ml", line 1, columns 34-45:
  1 | let invalid (values : int list) = to_sequence values
                                        ^^^^^^^^^^^
  Type Error: Unbound value to_sequence.
  [1]
