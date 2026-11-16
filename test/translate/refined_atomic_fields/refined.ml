type ('a, _) node = Null : ('a, [> `Null ]) node | Node : 'a -> ('a, [> `Node ]) node
type _ mode = Bool : bool mode | Unit : unit mode
type unused = { mutable marker : int [@caravan.frozen] }

let create (value : ('a, [ `Node ]) node) = Atomic.make value

let access : type a r. (a, [ `Node ]) node Atomic.t -> (a, [ `Node ]) node -> r mode -> r
    =
 fun cell replacement mode ->
  let previous = Atomic.get cell in
  let swapped = Atomic.compare_and_set cell previous replacement in
  match mode with Bool -> swapped | Unit -> ()

let broad_get (cell : ('a, [ `Null | `Node ]) node Atomic.t) = Atomic.get cell

let null_client () =
  let cell = Atomic.make Null in
  broad_get cell

let client value =
  let node : (_, [ `Node ]) node = Node value in
  let cell = create node in
  let _ = access cell node Bool in
  access cell node Unit
