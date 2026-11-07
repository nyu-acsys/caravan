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

A loop that may raise maintains what holds when it does: the function's raises clauses
if the exception leaves the function, or the loop's own. Its condition may not raise yet.

  $ caravan --shh loop_wrong.ml
  [Error] File "loop_wrong.ml", line 6, column 2 to line 10, column 6:
  6 |   while !i < n do
        ^^^^^^^^^^^^^^^
  Verification Error: This loop invariant may not be maintained.
  File "loop_wrong.ml", line 14, columns 21-26:
  14 |     raises Stop k -> k = a *)
                            ^^^^^
  Related Location: This assertion may not hold.
  [1]
  $ caravan --shh loop_clause_wrong.ml
  [Error] File "loop_clause_wrong.ml", line 7, column 5 to line 12, column 9:
  7 |      while !i < n do
           ^^^^^^^^^^^^^^^
  Verification Error: This loop invariant may not be maintained.
  File "loop_clause_wrong.ml", line 9, columns 48-57:
  9 |            raises Stop m -> own i.contents a && m = a + 1 *)
                                                      ^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
  $ caravan --shh loop_condition.ml
  [Error] File "loop_condition.ml", line 9, columns 8-19:
  9 |   while positive !i do
              ^^^^^^^^^^^
  Unsupported Error: A loop condition that may raise is not supported yet.
  [1]

A raise leaving a function with an atomic contract must follow the step that linearizes
it; what its atomic raises clauses say is checked; and a raising call in such a function
must linearize it, as a retry or a call of another atomic function before it has
linearized: a second call after the first is rejected.

  $ mkdir early wrong twice
  $ cp atomic_stack.ml atomic_stack.mli early/
  $ grep -v pop_exn atomic_stack.proof > early/atomic_stack.proof
  $ caravan --shh early/atomic_stack.ml
  [Error] File "early/atomic_stack.ml", line 14, columns 10-21:
  14 |   | [] -> raise Empty
                 ^^^^^^^^^^^
  Type Error: This raise may leave the function before a step linearizes it, or after it linearized returning: annotate the step that linearizes it by raising, as (*@ returning [] -> commit *).
  [1]
  $ cp atomic_stack.ml atomic_stack.proof wrong/
  $ sed 's/xs = \[\] && stack t \[\]/xs <> [] \&\& stack t []/' atomic_stack.mli > wrong/atomic_stack.mli
  $ caravan --shh wrong/atomic_stack.ml
  [Error] File "wrong/atomic_stack.ml", line 13, columns 8-20:
  13 |   match Atomic.get t with
               ^^^^^^^^^^^^
  Verification Error: The atomic postcondition may not hold after this step, which linearizes the function.
  File "wrong/atomic_stack.mli", line 22, columns 27-49:
  22 |     atomic raises Empty -> xs <> [] && stack t [] *)
                                  ^^^^^^^^^^^^^^^^^^^^^^
  Related Location: The atomic postcondition.
  [Error] File "wrong/atomic_stack.ml", line 13, columns 8-20:
  13 |   match Atomic.get t with
               ^^^^^^^^^^^^
  Verification Error: A postcondition may not hold at this return point.
  File "wrong/atomic_stack.mli", line 22, columns 27-35:
  22 |     atomic raises Empty -> xs <> [] && stack t [] *)
                                  ^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
  $ cp atomic_stack.ml atomic_stack.mli atomic_stack.proof twice/
  $ chmod u+w twice/atomic_stack.ml twice/atomic_stack.mli
  $ cat atomic_stack_twice.ml >> twice/atomic_stack.ml
  $ cat atomic_stack_twice.mli >> twice/atomic_stack.mli
  $ caravan --shh twice/atomic_stack.ml
  [Error] File "twice/atomic_stack.ml", line 19, columns 2-11:
  19 |   pop_exn t
         ^^^^^^^^^
  Unsupported Error: A call that may raise, other than a retry, in a function with an atomic contract is not supported yet.
  [1]
