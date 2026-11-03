A function's contract declares what it may raise, directly or by its calls.

  $ caravan --shh undeclared_call.ml
  [Error] File "undeclared_call.ml", line 7, columns 15-22:
  7 | let first xs = head xs
                     ^^^^^^^
  Type Error: This may raise Empty, which the contract of the function does not declare: add a raises clause.
  [1]
  $ caravan --shh undeclared_raise.ml
  [Error] File "undeclared_raise.ml", line 4, columns 61-72:
  4 | let check n = if n < 0 then raise (Bad n) else if n = 0 then raise Empty else n
                                                                   ^^^^^^^^^^^
  Type Error: This may raise Empty, which the contract of the function does not declare: add a raises clause.
  [1]

What a raises clause says must hold when the function raises.

  $ caravan --shh wrong_post.ml
  [Error] File "wrong_post.ml", line 3, columns 47-58:
  3 | let head (xs : int list) = match xs with [] -> raise Empty | x :: _ -> x
                                                     ^^^^^^^^^^^
  Verification Error: A postcondition may not hold at this return point.
  File "wrong_post.ml", line 5, columns 20-28:
  5 |     raises Empty -> xs <> [] *)
                          ^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

Raising in a loop is not supported yet.

  $ caravan --shh in_loop.ml
  [Error] File "in_loop.ml", line 6, columns 19-29:
  6 |     if !i = 5 then raise Stop;
                         ^^^^^^^^^^
  Unsupported Error: Raising an exception in a loop is not supported yet.
  [1]
