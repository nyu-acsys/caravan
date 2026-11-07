  $ caravan --shh wrong_result.ml
  [Error] File "wrong_result.ml", line 5, columns 82-82:
  5 |     match Stack.pop_opt stack with None -> [] | Some value -> value :: drain stack
                                                                                        ^
  Verification Error: A postcondition may not hold at this return point.
  File "wrong_result.ml", line 8, columns 38-51:
  8 |       ensures Stack.stack stack [] && result === [] *)
                                            ^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ caravan --shh wrong_contents.ml
  [Error] File "wrong_contents.ml", line 5, columns 82-82:
  5 |     match Stack.pop_opt stack with None -> [] | Some value -> value :: drain stack
                                                                                        ^
  Verification Error: A postcondition may not hold at this return point.
  File "wrong_contents.ml", line 8, columns 14-34:
  8 |       ensures Stack.stack stack xs && result === xs *)
                    ^^^^^^^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]
