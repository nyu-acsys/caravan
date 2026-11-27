type ('a, _) node = Null : ('a, [> `Null ]) node | Node : 'a -> ('a, [> `Node ]) node

let identity (node : ('a, ([> `Node ] as 's)) node) = node
