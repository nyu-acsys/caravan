  $ caravan --shh body_fail.ml
  [Error] File "body_fail.ml", line 9, columns 27-27:
  9 |   let incorrect (x : t) = x
                                 ^
  Verification Error: A postcondition may not hold at this return point.
  File "body_fail.ml", line 10, columns 35-40:
  10 |   (*@ result = incorrect x ensures false *)
                                          ^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ caravan --shh false_post_fail.ml
  [Error] File "false_post_fail.ml", line 14, columns 38-38:
  14 | let incorrect () = Instance.identity 7
                                             ^
  Verification Error: A postcondition may not hold at this return point.
  File "false_post_fail.ml", line 15, columns 34-44:
  15 | (*@ result = incorrect () ensures result = 8 *)
                                         ^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ caravan --shh distinct_fail.ml
  [Error] File "distinct_fail.ml", line 15, columns 41-42:
  15 | let incorrect (x : First.t) : Second.t = x
                                                ^
  Type Error: The value x has type First.t = Make(A)(B).t
  but an expression was expected of type Second.t = Make(A)(C).t.
  [1]

  $ caravan --shh trailing_unit_fail.ml
  [Error] File "trailing_unit_fail.ml", line 14, columns 41-42:
  14 | let incorrect (x : First.t) : Second.t = x
                                                ^
  Type Error: The value x has type First.t but an expression was expected of type Second.t.
  [1]

  $ caravan --shh first_argument_fail.ml
  [Error] File "first_argument_fail.ml", line 16, columns 29-29:
  16 | module Partial = Make (Wrong)
                                    ^
  Verification Error: The module argument does not establish this view's postcondition.
  File "first_argument_fail.ml", line 2, columns 2-27:
  2 |   val identity : int -> int
        ^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: The requested module operation.
  File "first_argument_fail.ml", line 7, columns 2-28:
  7 |   let identity (x : int) = 0
        ^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: The actual module operation.
  [1]

  $ caravan --shh second_argument_fail.ml
  [Error] File "second_argument_fail.ml", line 22, columns 33-33:
  22 | module Instance = Partial (Wrong)
                                        ^
  Verification Error: The module argument does not establish this view's postcondition.
  File "second_argument_fail.ml", line 2, columns 2-27:
  2 |   val identity : int -> int
        ^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: The requested module operation.
  File "second_argument_fail.ml", line 12, columns 2-28:
  12 |   let identity (x : int) = 0
         ^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: The actual module operation.
  [1]

  $ caravan --shh anonymous_argument_fail.ml
  [Error] File "anonymous_argument_fail.ml", line 6, columns 27-37:
  6 | module Instance = Partial (struct end)
                                 ^^^^^^^^^^
  Unsupported Error: A non-path functor argument is not supported yet.
  [1]

  $ caravan --shh -I ../functors opaque_resource_fail.ml
  [Error] File "opaque_resource_fail.ml", line 20, columns 19-34:
  20 | module Incorrect = Partial (Right)
                          ^^^^^^^^^^^^^^^
  Type Error: The resource declaration counter has different parameter types.
  [1]
