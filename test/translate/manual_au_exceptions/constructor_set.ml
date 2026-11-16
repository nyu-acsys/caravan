type ('a, _) node =
  | Null : ('a, [> `Null ]) node
  | Node : 'a Atomic.t -> ('a, [> `Node ]) node

type ('a, _) kind = Value : ('a, 'a) kind | Option : ('a, 'a option) kind

let read_as : type a r. (a, [ `Node ]) node -> (a, r) kind -> r =
 fun node kind ->
  match node with
  | Node cell -> (
      let value = Atomic.get cell in
      match kind with Value -> value | Option -> Some value)

let read (node : ('a, [ `Node ]) node) = match node with Node cell -> Atomic.get cell
