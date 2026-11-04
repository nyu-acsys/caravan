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

An exception that a handler does not catch, or re-raises, must be declared; what a
handler computes is checked.

  $ caravan --shh handler_leak.ml
  [Error] File "handler_leak.ml", line 13, columns 23-58:
  13 | let first_checked xs = try check (head xs) with Bad _ -> 0
                              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: This may raise Empty, which the contract of the function does not declare: add a raises clause.
  [1]
  $ caravan --shh handler_reraise.ml
  [Error] File "handler_reraise.ml", line 9, columns 37-44:
  9 | let first xs = try head xs with e -> raise e
                                           ^^^^^^^
  Type Error: This may raise Empty, which the contract of the function does not declare: add a raises clause.
  [1]
  $ caravan --shh handler_wrong.ml
  [Error] File "handler_wrong.ml", line 8, columns 46-46:
  8 | let head_or xs d = try head xs with Empty -> d
                                                    ^
  Verification Error: A postcondition may not hold at this return point.
  File "handler_wrong.ml", line 10, columns 12-18:
  10 |     ensures r <> d *)
                   ^^^^^^
  Related Location: This assertion may not hold.
  [1]
