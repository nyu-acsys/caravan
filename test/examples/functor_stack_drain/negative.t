  $ caravan --shh wrong_result.ml
  [Error] File "wrong_result.ml", line 15, columns 82-82:
  15 |     match Stack.pop_opt stack with None -> [] | Some value -> value :: drain stack
                                                                                         ^
  Verification Error: A postcondition may not hold at this return point.
  File "wrong_result.ml", line 18, columns 38-49:
  18 |       ensures Stack.stack stack [] && result = [] *)
                                             ^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ caravan --shh wrong_contents.ml
  [Error] File "wrong_contents.ml", line 15, columns 82-82:
  15 |     match Stack.pop_opt stack with None -> [] | Some value -> value :: drain stack
                                                                                         ^
  Verification Error: A postcondition may not hold at this return point.
  File "wrong_contents.ml", line 18, columns 14-34:
  18 |       ensures Stack.stack stack xs && result = xs *)
                     ^^^^^^^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]
