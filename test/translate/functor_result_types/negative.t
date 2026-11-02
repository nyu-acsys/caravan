  $ caravan --shh false_post_fail.ml
  [Error] File "false_post_fail.ml", line 15, columns 48-48:
  15 | let incorrect () = Right.identity (Left.Value 7)
                                                       ^
  Verification Error: A postcondition may not hold at this return point.
  File "false_post_fail.ml", line 16, columns 34-55:
  16 | (*@ result = incorrect () ensures result = Left.Value 8 *)
                                         ^^^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ caravan --shh distinct_fail.ml
  [Error] File "distinct_fail.ml", line 13, columns 41-42:
  13 | let incorrect (x : First.t) : Second.t = x
                                                ^
  Type Error: The value x has type First.t = Make(First_argument).t
  but an expression was expected of type Second.t = Make(Second_argument).t.
  [1]

  $ caravan --shh sealed_fail.ml
  [Error] File "sealed_fail.ml", line 19, columns 41-42:
  19 | let incorrect (x : First.t) : Second.t = x
                                                ^
  Type Error: The value x has type First.t = Make(First_view).t
  but an expression was expected of type Second.t = Make(Second_view).t.
  [1]

  $ caravan --shh body_fail.ml
  [Error] File "body_fail.ml", line 8, columns 27-27:
  8 |   let incorrect (x : t) = x
                                 ^
  Verification Error: A postcondition may not hold at this return point.
  File "body_fail.ml", line 9, columns 35-51:
  9 |   (*@ result = incorrect x ensures result = Value 0 *)
                                         ^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ caravan --shh sealed_nested_fail.ml
  [Error] File "sealed_nested_fail.ml", line 28, columns 41-42:
  28 | let incorrect (x : First.t) : Second.t = x
                                                ^
  Type Error: The value x has type First.t = Make(First_view.Arg).t
  but an expression was expected of type Second.t = Make(Second_view.Arg).t.
  [1]
