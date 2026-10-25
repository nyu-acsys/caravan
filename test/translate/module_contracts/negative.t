  $ caravan --shh abort_restoration_fail.ml
  [Error] File "abort_restoration_fail.ml", line 1, column 15 to line 11, column 14:
  1 | module Checked : sig
                     ^^^^^
  Verification Error: This view's atomic update may not be restorable if the actual operation aborts.
  File "abort_restoration_fail.ml", line 6, columns 2-21:
  6 |   val read : t -> int
        ^^^^^^^^^^^^^^^^^^^
  Related Location: The requested module operation.
  File "./abort_actual.mli", line 5, columns 0-19:
  5 | val read : t -> int
      ^^^^^^^^^^^^^^^^^^^
  Related Location: The actual module operation.
  [1]

  $ caravan --shh atomic_hidden_post_fail.ml
  [Error] File "atomic_hidden_post_fail.ml", line 21, columns 9-21:
  21 |   assert (result = 7)
                ^^^^^^^^^^^^
  Verification Error: This assertion may be violated.
  [1]

  $ caravan --shh atomic_post_fail.ml
  [Error] File "atomic_post_fail.ml", line 13, columns 15-43:
  13 | module Checked : View = Actual.Atomic_first
                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: The module argument does not establish this view's atomic postcondition.
  File "atomic_post_fail.ml", line 6, columns 2-21:
  6 |   val read : t -> int
        ^^^^^^^^^^^^^^^^^^^
  Related Location: The requested module operation.
  File "./actual.mli", line 18, columns 2-21:
  18 |   val read : t -> int
         ^^^^^^^^^^^^^^^^^^^
  Related Location: The actual module operation.
  [Error] File "atomic_post_fail.ml", line 13, columns 15-43:
  13 | module Checked : View = Actual.Atomic_first
                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: The module argument does not establish this view's postcondition.
  File "atomic_post_fail.ml", line 6, columns 2-21:
  6 |   val read : t -> int
        ^^^^^^^^^^^^^^^^^^^
  Related Location: The requested module operation.
  File "./actual.mli", line 18, columns 2-21:
  18 |   val read : t -> int
         ^^^^^^^^^^^^^^^^^^^
  Related Location: The actual module operation.
  [1]

  $ caravan --shh atomic_pre_fail.ml
  [Error] File "atomic_pre_fail.ml", line 13, columns 15-50:
  13 | module Checked : View = Actual.Strong_Atomic_first
                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: The module argument's precondition is not provided by this view.
  File "atomic_pre_fail.ml", line 6, columns 2-21:
  6 |   val read : t -> int
        ^^^^^^^^^^^^^^^^^^^
  Related Location: The requested module operation.
  File "./actual.mli", line 47, columns 2-21:
  47 |   val read : t -> int
         ^^^^^^^^^^^^^^^^^^^
  Related Location: The actual module operation.
  [1]

  $ caravan --shh explicit_ghost_fail.ml
  [Error] File "explicit_ghost_fail.ml", line 6, columns 2-21:
  6 |   val read : t -> int
        ^^^^^^^^^^^^^^^^^^^
  Unsupported Error: Explicit ghost inputs or outputs in a checked module binding is not supported yet.
  [1]

  $ caravan --shh explicit_output_fail.ml
  [Error] File "explicit_output_fail.ml", line 6, columns 2-21:
  6 |   val read : t -> int
        ^^^^^^^^^^^^^^^^^^^
  Unsupported Error: Explicit ghost inputs or outputs in a checked module binding is not supported yet.
  [1]

  $ caravan --shh kind_fail.ml
  [Error] File "kind_fail.ml", line 13, columns 15-36:
  13 | module Checked : View = Actual.First
                      ^^^^^^^^^^^^^^^^^^^^^
  Type Error: The module operation has a different ordinary or logically atomic contract kind.
  [1]

  $ caravan --shh missing_predicate_fail.ml
  [Error] File "missing_predicate_fail.ml", line 13, columns 15-36:
  13 | module Checked : View = Actual.First
                      ^^^^^^^^^^^^^^^^^^^^^
  Type Error: The actual module does not declare resource missing.
  [1]

  $ caravan --shh ordinary_hidden_post_fail.ml
  [Error] File "ordinary_hidden_post_fail.ml", line 19, columns 9-21:
  19 |   assert (result = 7)
                ^^^^^^^^^^^^
  Verification Error: This assertion may be violated.
  [1]

  $ caravan --shh ordinary_post_fail.ml
  [Error] File "ordinary_post_fail.ml", line 13, columns 36-36:
  13 | module Checked : View = Actual.First
                                           ^
  Verification Error: The module argument does not establish this view's postcondition.
  File "ordinary_post_fail.ml", line 6, columns 2-21:
  6 |   val read : t -> int
        ^^^^^^^^^^^^^^^^^^^
  Related Location: The requested module operation.
  File "./actual.mli", line 6, columns 2-21:
  6 |   val read : t -> int
        ^^^^^^^^^^^^^^^^^^^
  Related Location: The actual module operation.
  [1]

  $ caravan --shh ordinary_pre_fail.ml
  [Error] File "ordinary_pre_fail.ml", line 13, columns 15-43:
  13 | module Checked : View = Actual.Strong_First
                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: The module argument's precondition is not provided by this view.
  File "ordinary_pre_fail.ml", line 6, columns 2-21:
  6 |   val read : t -> int
        ^^^^^^^^^^^^^^^^^^^
  Related Location: The requested module operation.
  File "./actual.mli", line 35, columns 2-21:
  35 |   val read : t -> int
         ^^^^^^^^^^^^^^^^^^^
  Related Location: The actual module operation.
  [1]

  $ caravan --shh predicate_arity_fail.ml
  [Error] File "predicate_arity_fail.ml", line 13, columns 15-36:
  13 | module Checked : View = Actual.First
                      ^^^^^^^^^^^^^^^^^^^^^
  Type Error: The resource declaration counter has a different kind or arity.
  [1]

  $ caravan --shh predicate_kind_fail.ml
  [Error] File "predicate_kind_fail.ml", line 13, columns 15-36:
  13 | module Checked : View = Actual.First
                      ^^^^^^^^^^^^^^^^^^^^^
  Type Error: The resource declaration counter has a different kind or arity.
  [1]

  $ caravan --shh predicate_modes_fail.ml
  [Error] File "predicate_modes_fail.ml", line 13, columns 15-36:
  13 | module Checked : View = Actual.First
                      ^^^^^^^^^^^^^^^^^^^^^
  Type Error: The resource declaration counter has different implicit parameter modes.
  [1]

  $ caravan --shh predicate_type_fail.ml
  [Error] File "predicate_type_fail.ml", line 13, columns 15-36:
  13 | module Checked : View = Actual.First
                      ^^^^^^^^^^^^^^^^^^^^^
  Type Error: The resource declaration counter has different parameter types.
  [1]

  $ caravan --shh unused_member_fail.ml
  [Error] File "unused_member_fail.ml", line 13, columns 36-36:
  13 | module Checked : View = Actual.First
                                           ^
  Verification Error: The module argument does not establish this view's postcondition.
  File "unused_member_fail.ml", line 6, columns 2-21:
  6 |   val read : t -> int
        ^^^^^^^^^^^^^^^^^^^
  Related Location: The requested module operation.
  File "./actual.mli", line 6, columns 2-21:
  6 |   val read : t -> int
        ^^^^^^^^^^^^^^^^^^^
  Related Location: The actual module operation.
  [1]

  $ caravan --shh source_opacity_fail.ml
  [Error] File "source_opacity_fail.ml", line 19, columns 34-35:
  19 |     requires Actual.First.counter x state && state >= 0 && Checked.ticket x 7
                                         ^
  Type Error: This specification has type Checked.t, but Actual.First.t is required.
  [1]

  $ caravan --shh source_cross_view_fail.ml
  [Error] File "source_cross_view_fail.ml", line 20, columns 27-28:
  20 |     requires Right.counter x state && state >= 0 && Left.ticket x 7
                                  ^
  Type Error: This specification has type Left.t, but Right.t is required.
  [1]

  $ caravan --shh mli_strengthening_fail.ml
  [Error] File "mli_strengthening_fail.mli", line 2, columns 2-20:
  2 |   val f : int -> int
        ^^^^^^^^^^^^^^^^^^
  Unsupported Error: An additional interface contract on a checked module view is not supported yet.
  [1]

  $ caravan --shh double_constraint_fail.ml
  [Error] File "double_constraint_fail.ml", line 11, columns 15-39:
  11 | module Checked : S = (Actual_local : S)
                      ^^^^^^^^^^^^^^^^^^^^^^^^
  Unsupported Error: Nested inline constraints on a checked module view is not supported yet.
  [1]

  $ caravan --shh mli_unannotated_fail.ml
  [Error] File "mli_unannotated_fail.mli", line 2, columns 2-20:
  2 |   val f : int -> int
        ^^^^^^^^^^^^^^^^^^
  Unsupported Error: An additional interface contract on a checked module view is not supported yet.
  [1]

  $ caravan --shh unresolved_namespace_fail.ml
  [Error] File "unresolved_namespace_fail.ml", line 4, columns 22-36:
  4 | (*@ client x requires view_checked_0.counter x 0 *)
                            ^^^^^^^^^^^^^^
  Type Error: Unbound name view_checked_0.
  [1]

  $ caravan --shh defined_signature_fail.ml
  [Error] File "./formal_api.mli", line 4, columns 2-64:
  4 |   (*@ predicate counter (x : t) (n [@implicit] : int) = false *)
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Unsupported Error: A resource definition in a checked module signature is not supported yet.
  [1]

  $ caravan --shh inferred_pure_post_fail.ml
  [Error] File "inferred_pure_post_fail.ml", line 15, columns 29-29:
  15 | let client x = Checked.read x
                                    ^
  Verification Error: A postcondition may not hold at this return point.
  File "inferred_pure_post_fail.ml", line 16, columns 56-70:
  16 | (*@ result = client x requires 0 <= x < max_int ensures result = x + 1 *)
                                                               ^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ caravan --shh constant_member_fail.ml
  [Error] File "constant_member_fail.ml", line 2, columns 2-19:
  2 |   val answer : bool
        ^^^^^^^^^^^^^^^^^
  Unsupported Error: A non-function value in a checked module signature is not supported yet.
  [1]

  $ caravan --shh implicit_opaque_fail.ml
  [Error] File "implicit_opaque_fail.ml", line 14, columns 55-60:
  14 |   (*@ result = read x requires own x.contents value && value >= 0 ensures own x.contents value && result = value *)
                                                              ^^^^^
  Type Error: This specification has type state, but int is required.
  [1]

  $ caravan --shh opaque_ownership_fail.ml
  [Error] File "opaque_ownership_fail.ml", line 14, columns 48-49:
  14 |   (*@ result = read x n requires own x.contents n ensures own x.contents n *)
                                                       ^
  Type Error: This specification has type int, but state is required.
  [1]

  $ caravan --shh opaque_collection_fail.ml
  [Error] File "opaque_collection_fail.ml", line 15, columns 56-62:
  15 |       ensures forall values: state finset. Finset.mem 0 values <-> Finset.mem 0 values *)
                                                               ^^^^^^
  Type Error: The value values has type state finset but an expression was expected of type
    int finset
  Type state is not compatible with type int.
  [1]

  $ caravan --shh same_actual_opaque_fail.ml
  [Error] File "same_actual_opaque_fail.ml", line 17, columns 27-28:
  17 |     requires Right.counter x state
                                  ^
  Type Error: This specification has type Left.t, but Right.t is required.
  [1]
