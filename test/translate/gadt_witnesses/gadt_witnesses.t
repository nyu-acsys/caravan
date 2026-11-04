A GADT whose constructors are constant is a witness: its tags are a data type, and its
witnesses implement one interface, with the value dictionaries of its parameters and
conversions from each constructor's index types.

  $ caravan --shh declarations.ml
  Verification successful.

Several ordinary parameters, index types built from them, and a witness in a module.

  $ caravan --shh shapes.ml
  Verification successful.

A function with a witness parameter is a worker over the witness, which its callers pass:
a constructor's implementation, or their own. A match on the witness converts each case's
value to the type that the witness selects.

  $ caravan --shh functions.ml
  Verification successful.
  $ caravan --shh forwarded.ml
  Verification successful.
  $ caravan --shh stateful.ml
  Verification successful.

The emitted program verifies too.

  $ caravan --shh --emit-rav functions.ml > functions.rav
  $ raven --shh functions.rav
  Verification successful.

A witness argument other than a constructor or the caller's own witness is rejected.

  $ caravan --shh witness_value.ml
  [Error] File "witness_value.ml", line 8, columns 8-9:
  8 |   get x w
              ^
  Unsupported Error: A witness argument other than a constructor or the caller's own witness is not supported yet.
  [1]

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
