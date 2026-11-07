type boxed = Box of int
type record = { number : int; items : int list }
type tree = Leaf | Node of tree * int * tree

let first (items : int list) = match items with [] -> 0 | head :: _ -> head
(*@ result = first items pure ensures (-4611686018427387903 - 1) <= result && result <= 4611686018427387903 *)

let option_value (value : int option) = match value with None -> 0 | Some value -> value
(*@ result = option_value value ensures (-4611686018427387903 - 1) <= result && result <= 4611686018427387903 *)

let tuple_value ((value, _) : int * bool) = value
(*@ result = tuple_value pair ensures (-4611686018427387903 - 1) <= result && result <= 4611686018427387903 *)

let boxed_value (value : boxed) = match value with Box number -> number
(*@ result = boxed_value value ensures (-4611686018427387903 - 1) <= result && result <= 4611686018427387903 *)

let record_value (value : record) = (value.number, value.items)
(*@ result = record_value value ensures result === (value.number, value.items) *)

let tree_value (value : tree) =
  match value with Leaf -> 0 | Node (_, number, _) -> number
(*@ result = tree_value value ensures (-4611686018427387903 - 1) <= result && result <= 4611686018427387903 *)

let stored (items : int list) =
  let cell = ref items in
  let previous = !cell in
  cell := [ first previous ];
  first !cell
(*@ result = stored items ensures (-4611686018427387903 - 1) <= result && result <= 4611686018427387903 *)

let atomic_store (items : int list) =
  let cell = Atomic.make items in
  let previous = Atomic.exchange cell [ 0 ] in
  first previous
(*@ result = atomic_store items ensures (-4611686018427387903 - 1) <= result && result <= 4611686018427387903 *)

let quantified () = ()
(*@ quantified () ensures forall items : int list. (-4611686018427387903 - 1) <= first items && first items <= 4611686018427387903 *)

let repeated (items : int list) =
  for index = 0 to 1 do
    let _ = first items in
    assert (index <= 1)
  done

type storage = { mutable contents : int option list }

let recorded (items : int option list) =
  let cell = { contents = items } in
  cell.contents <- Some 0 :: cell.contents;
  cell.contents

type forest = Forest of int * forest list

let root (value : forest) = match value with Forest (number, _) -> number
(*@ result = root value ensures min_int <= result && result <= max_int *)

let roots (values : forest list) = match values with [] -> 0 | value :: _ -> root value
(*@ result = roots values ensures min_int <= result && result <= max_int *)
