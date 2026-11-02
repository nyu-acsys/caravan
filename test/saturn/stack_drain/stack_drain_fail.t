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
