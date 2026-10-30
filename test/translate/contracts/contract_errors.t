Each function stops the run at its first error, so each has its own run.

  $ caravan --shh contract_error_1.ml
  [Error] File "contract_error_1.ml", line 2, columns 8-9:
  2 | (*@ r = g x
              ^
  Type Error: This contract is for g, not f.
  [1]
  $ caravan --shh contract_error_2.ml
  [Error] File "contract_error_2.ml", line 2, columns 8-9:
  2 | (*@ r = h x y *)
              ^
  Type Error: This contract names 2 arguments, but h has 1.
  [1]
  $ caravan --shh contract_error_3.ml
  [Error] File "contract_error_3.ml", line 3, columns 16-17:
  3 |     ensures r = y *)
                      ^
  Type Error: Unbound name y.
  [1]
  $ caravan --shh contract_error_4.ml
  [Error] File "contract_error_4.ml", line 3, columns 19-20:
  3 |     ensures forall y. y = y *)
                         ^
  Type Error: A bound variable needs a type, as in x: int.
  [1]
  $ caravan --shh contract_error_5.ml
  [Error] File "contract_error_5.ml", line 3, columns 16-17:
  3 |     ensures r = = x *)
                      ^
  Syntax Error: Syntax error.
  [1]
