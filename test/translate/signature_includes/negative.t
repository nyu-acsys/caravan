  $ caravan --shh wrong_body.ml
  [Error] File "wrong_body.ml", line 11, columns 33-33:
  11 |   let identity (_value : int) = 0
                                        ^
  Verification Error: A postcondition may not hold at this return point.
  File "wrong_body.ml", line 3, columns 38-52:
  3 |   (*@ result = identity value ensures result = value *)
                                            ^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ caravan --shh resource_wrong.ml
  [Error] File "resource_wrong.ml", line 16, columns 15-43:
  16 | module Checked : Extended = Resource_actual
                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: The resource declaration owned has different parameter types.
  [1]

  $ caravan --shh resource_conflict_before.ml
  [Error] File "resource_conflict_before.ml", line 7, columns 2-14:
  7 |   include Base
        ^^^^^^^^^^^^
  Type Error: The included resource owned is already declared.
  [1]

  $ caravan --shh resource_conflict_after.ml
  [Error] File "resource_conflict_after.ml", line 6, columns 2-14:
  6 |   include Base
        ^^^^^^^^^^^^
  Type Error: The included resource owned is already declared.
  [1]

  $ caravan --shh proof_module.ml
  [Error] File "proof_module.ml", line 6, columns 2-14:
  6 |   include Base
        ^^^^^^^^^^^^
  Unsupported Error: An include of a signature with abstract proof modules is not supported yet.
  [1]
