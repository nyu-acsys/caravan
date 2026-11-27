type ('a, _) node = Null : ('a, [> `Null ]) node | Node : 'a -> ('a, [> `Node ]) node

let bad (Node value : (int, [ `Null | `Node ]) node) = value
