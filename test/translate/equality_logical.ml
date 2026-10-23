type node = End | Next of int ref

let lists (cell : int ref) = ([ cell ], [ cell ])
(*@ result = lists cell ensures match result with (left, right) -> left === right *)

let fresh () =
  let left = ref 0 in
  let right = ref 0 in
  (left, right)
(*@ result = fresh () ensures match result with (left, right) ->
    own left.contents 0 && own right.contents 0
    && left =/= right && not (left === right) *)
