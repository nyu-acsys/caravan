type ('a, _) node =
  | Null : ('a, [> `Null ]) node
  | Node : { mutable value : 'a } -> ('a, [> `Node ]) node

let write (node : ('a, [ `Node ]) node) value =
  match node with Node record -> record.value <- value
