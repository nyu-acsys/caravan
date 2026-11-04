A GADT whose constructors are constant is a witness: its tags are a data type, and its
witnesses implement one interface, with the value dictionaries of its parameters and
conversions from each constructor's index types.

  $ caravan --shh declarations.ml
  Verification successful.

Several ordinary parameters, index types built from them, and a witness in a module.

  $ caravan --shh shapes.ml
  Verification successful.

Constructors with payloads, and index types with variables of their own, are rejected.

  $ caravan --shh payload.ml
  [Error] File "payload.ml", line 1, columns 16-42:
  1 | type (_, _) t = Boxed : int -> ('a, int) t
                      ^^^^^^^^^^^^^^^^^^^^^^^^^^
  Unsupported Error: A GADT beyond constant witnesses is not supported yet.
  [1]
  $ caravan --shh existential.ml
  [Error] File "existential.ml", line 1, columns 16-38:
  1 | type (_, _) t = Wrap : ('a, 'b list) t
                      ^^^^^^^^^^^^^^^^^^^^^^
  Unsupported Error: A GADT beyond constant witnesses is not supported yet.
  [1]
