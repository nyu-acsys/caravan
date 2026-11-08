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

Each domain must complete all ten pushes before returning its completion resources.

  $ mkdir short_worker
  $ cp stack_drain.mli stack_drain.proof stack_intf.mli treiber_stack.mli short_worker/
  $ sed 's/for i = 0 to 9 do/for i = 0 to 8 do/' stack_drain.ml > short_worker/stack_drain.ml
  $ ! caravan --shh short_worker/stack_drain.ml > short_worker.out 2>&1
  $ grep -q 'Verification Error: A postcondition may not hold' short_worker.out
  $ ! grep -Eq 'Unsupported Error:|Internal Error:|timed out' short_worker.out

A join is required before its worker contribution can be recovered for draining.

  $ mkdir missing_join
  $ cp stack_drain.mli stack_drain.proof stack_intf.mli treiber_stack.mli missing_join/
  $ sed '/    Domain.join domainB;/d' stack_drain.ml > missing_join/stack_drain.ml
  $ ! caravan --shh missing_join/stack_drain.ml > missing_join.out 2>&1
  $ grep -q 'Verification Error:' missing_join.out
  $ ! grep -Eq 'Unsupported Error:|Internal Error:|timed out' missing_join.out

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
