  $ caravan --shh distinct_fail.ml
  [Error] File "distinct_fail.ml", line 9, columns 41-42:
  9 | let incorrect (x : First.t) : Second.t = x
                                               ^
  Type Error: The value x has type First.t but an expression was expected of type Second.t.
  [1]

  $ caravan --shh body_fail.ml
  [Error] File "body_fail.ml", line 4, columns 27-27:
  4 |   let incorrect (x : t) = x
                                 ^
  Verification Error: A postcondition may not hold at this return point.
  File "body_fail.ml", line 5, columns 35-51:
  5 |   (*@ result = incorrect x ensures result = Value 0 *)
                                         ^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ caravan --shh false_post_fail.ml
  [Error] File "false_post_fail.ml", line 10, columns 55-55:
  10 | let incorrect () = Instance.identity (Instance.Value 7)
                                                              ^
  Verification Error: A postcondition may not hold at this return point.
  File "false_post_fail.ml", line 11, columns 34-59:
  11 | (*@ result = incorrect () ensures result = Instance.Value 8 *)
                                         ^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ caravan --shh named_fresh_fail.ml
  [Error] File "named_fresh_fail.ml", line 8, columns 20-30:
  8 |   module Instance = Factory ()
                          ^^^^^^^^^^
  Type Error: This expression creates fresh types.
  It is not allowed inside applicative functors..
  [1]

  $ caravan --shh named_distinct_fail.ml
  [Error] File "named_distinct_fail.ml", line 18, columns 39-40:
  18 | let incorrect (x : Left.t) : Right.t = x
                                              ^
  Type Error: The value x has type Left.t = First.t but an expression was expected of type
    Right.t = Second.t.
  [1]
