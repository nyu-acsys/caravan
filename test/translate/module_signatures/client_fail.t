  $ caravan --shh wrong_body.ml
  [Error] File "wrong_body.ml", line 2, columns 61-61:
  2 |   let identity (value : int) = if value = 0 then 1 else value
                                                                   ^
  Verification Error: A postcondition may not hold at this return point.
  File "./contract_api.mli", line 5, columns 38-52:
  5 |   (*@ result = identity value ensures result = value *)
                                            ^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ caravan --shh constrained_alias.ml
  [Error] File "constrained_alias.ml", line 5, columns 49-49:
  5 | module Checked : Contract_api.Identity = Original
                                                       ^
  Verification Error: The module argument does not establish this view's postcondition.
  File "./contract_api.mli", line 4, columns 2-27:
  4 |   val identity : int -> int
        ^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: The requested module operation.
  File "constrained_alias.ml", line 2, columns 2-36:
  2 |   let identity (value : int) = value
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: The actual module operation.
  [1]

  $ caravan --shh abstract_contract.ml
  [Error] File "abstract_contract.ml", line 5, columns 38-44:
  5 |   (*@ result = identity value ensures result + 1 = value *)
                                            ^^^^^^
  Type Error: This specification has type t, but int is required.
  [1]

  $ caravan --shh abstract_predicate.ml
  [Error] File "abstract_predicate.ml", line 6, columns 15-40:
  6 |       requires Contract_api.number value
                     ^^^^^^^^^^^^^^^^^^^^^^^^^
  Unsupported Error: A predicate call involving an abstract signature type is not supported yet.
  [1]

  $ caravan --shh abstract_predicate_client.ml
  [Error] File "abstract_predicate_client.ml", line 12, columns 46-51:
  12 | (*@ client value requires Contract_api.number value *)
                                                     ^^^^^
  Type Error: This specification has type Sealed.t, but int is required.
  [1]
