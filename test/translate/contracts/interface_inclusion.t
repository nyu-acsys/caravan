Sibling interfaces are checked by OCaml's signature-inclusion checker.

Abstraction, private implementation bindings, and monomorphic specialization remain valid.

  $ caravan --shh interface_inclusion.ml
  Verification successful.

Incompatible value types, missing declarations, incompatible type declarations,
and insufficiently general implementations are rejected.

  $ caravan --shh interface_inclusion_type_fail.ml
  [Error] File "interface_inclusion_type_fail.mli", line 1, columns 0-27:
  1 | val identity : bool -> bool
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: Values do not match:
    val identity : int -> int
  is not included in
    val identity : bool -> bool
  The type int -> int is not compatible with the type bool -> bool
  Type int is not compatible with type bool
  File "interface_inclusion_type_fail.mli", line 1, characters 0-27:
    Expected declaration
  File "interface_inclusion_type_fail.ml", line 1, characters 4-12:
    Actual declaration.
  [1]

  $ caravan --shh interface_inclusion_missing_fail.ml
  [Error] File "interface_inclusion_missing_fail.mli", line 1, columns 0-26:
  1 | val missing : unit -> unit
      ^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: The value missing is required but not provided
  File "interface_inclusion_missing_fail.mli", line 1, characters 0-26:
    Expected declaration.
  [1]

  $ caravan --shh interface_inclusion_declaration_fail.ml
  [Error] File "interface_inclusion_declaration_fail.mli", line 1, columns 0-13:
  1 | type t = bool
      ^^^^^^^^^^^^^
  Type Error: Type declarations do not match: type t = int is not included in type t = bool
  The type int is not equal to the type bool
  File "interface_inclusion_declaration_fail.mli", line 1, characters 0-13:
    Expected declaration
  File "interface_inclusion_declaration_fail.ml", line 1, characters 0-12:
    Actual declaration.
  [1]

  $ caravan --shh interface_inclusion_generalization_fail.ml
  [Error] File "interface_inclusion_generalization_fail.mli", line 1, columns 0-23:
  1 | val identity : 'a -> 'a
      ^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: Values do not match:
    val identity : int -> int
  is not included in
    val identity : 'a -> 'a
  The type int -> int is not compatible with the type 'a -> 'a
  Type int is not compatible with type 'a
  File "interface_inclusion_generalization_fail.mli", line 1, characters 0-23:
    Expected declaration
  File "interface_inclusion_generalization_fail.ml", line 1, characters 4-12:
    Actual declaration.
  [1]

The interface cannot refer to undeclared implementation-private types.

  $ caravan --shh interface_inclusion_scope_fail.ml
  [Error] File "interface_inclusion_scope_fail.mli", line 1, columns 15-21:
  1 | val identity : hidden -> hidden
                     ^^^^^^
  Type Error: Unbound type constructor hidden.
  [1]
