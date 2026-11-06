Draining a nonempty stack cannot always return an empty list.

  $ caravan --shh wrong_result.ml
  [Error] File "wrong_result.ml", line 2, columns 88-88:
  2 |   match Treiber_stack.pop_opt stack with None -> [] | Some value -> value :: drain stack
                                                                                              ^
  Verification Error: A postcondition may not hold at this return point.
  File "wrong_result.ml", line 5, columns 44-57:
  5 |     ensures Treiber_stack.stack stack [] && result === [] *)
                                                  ^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

The instantiated generic loop must retain the value returned by each pop.

  $ mkdir wrong_loop
  $ cp stack_drain.mli stack_drain.proof stack_intf.mli treiber_stack.mli wrong_loop/
  $ sed 's/Some v -> v :: loop ()/Some v -> (match v :: loop () with [] -> [] | _ :: rest -> rest)/' stack_drain.ml > wrong_loop/stack_drain.ml
  $ ! caravan --shh wrong_loop/stack_drain.ml > wrong_loop.out 2>&1
  $ grep -q 'Verification Error: A postcondition may not hold' wrong_loop.out
  $ ! grep -Eq 'Unsupported Error:|Internal Error:|timed out' wrong_loop.out

Draining consumes the original contents rather than preserving them in the stack.

  $ caravan --shh wrong_contents.ml
  [Error] File "wrong_contents.ml", line 2, columns 88-88:
  2 |   match Treiber_stack.pop_opt stack with None -> [] | Some value -> value :: drain stack
                                                                                              ^
  Verification Error: A postcondition may not hold at this return point.
  File "wrong_contents.ml", line 5, columns 12-40:
  5 |     ensures Treiber_stack.stack stack xs && result === xs *)
                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]

A raise of the interface's function that the client's contract does not declare is
rejected.

  $ caravan --shh undeclared_raise.ml
  [Error] File "undeclared_raise.ml", line 1, columns 16-43:
  1 | let pop stack = Treiber_stack.pop_exn stack
                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: This may raise Treiber_stack.Empty, which the contract of the function does not declare: add a raises clause.
  [1]

A raises clause that the interface's contract does not imply fails.

  $ caravan --shh wrong_raise.ml
  [Error] File "wrong_raise.ml", line 1, columns 16-43:
  1 | let pop stack = Treiber_stack.pop_exn stack
                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: A postcondition may not hold at this return point.
  File "wrong_raise.ml", line 7, columns 34-42:
  7 |     raises Treiber_stack.Empty -> xs <> [] *)
                                        ^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
