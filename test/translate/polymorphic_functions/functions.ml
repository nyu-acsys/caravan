let id value = value
(*@ result = id value pure ensures result === value *)

let twice value = id (id value)
(*@ result = twice value pure ensures id value === result *)

let singleton value = id [ value ]
(*@ result = singleton value pure ensures result === [value] *)

let optional value = id (Some value)
(*@ result = optional value pure ensures result === Some value *)

let const value _ = value
(*@ result = const value ignored pure ensures result === value *)

let pair first second = (first, second)
(*@ result = pair first second pure ensures result === (first, second) *)

let swap (first, second) = (second, first)
(*@ result = swap input pure
    ensures match input with (first, second) -> result === (second, first) *)

let rec copy items = match items with [] -> [] | head :: tail -> head :: copy tail
(*@ result = copy items pure ensures result === items *)

let integers (value : int) =
  let first = id value in
  let second = const first false in
  let result = pair second true in
  swap result
(*@ result = integers value ensures result === (true, value) *)

let booleans (value : bool) =
  let first = id value in
  let second = const first 17 in
  swap (pair second 42)
(*@ result = booleans value ensures result === (42, value) *)

let lists (items : int list) = copy (id items)
(*@ result = lists items ensures result === items *)

let boolean_lists (items : bool list) = copy items
(*@ result = boolean_lists items ensures result === items *)

let containers (value : int) = (singleton value, optional (twice value))
(*@ result = containers value ensures result === ([value], Some value) *)

let logical_clients (value : int) (flag : bool) = ()
(*@ logical_clients value flag
    ensures id value === value
    ensures id flag === flag
    ensures const value flag === value
    ensures pair value flag === (value, flag)
    ensures swap (value, flag) === (flag, value)
    ensures copy [value] === [value] *)
