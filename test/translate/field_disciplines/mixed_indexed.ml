type ('a, _) node =
  | Null : ('a, [> `Null ]) node
  | Node : {
      next : 'a link Atomic.t;
      mutable value : 'a; [@caravan.relaxed]
      mutable capacity : int; [@caravan.relaxed]
      mutable counter : int; [@caravan.frozen]
    }
      -> ('a, [> `Node ]) node

and 'a link = Link : ('a, [< `Null | `Node ]) node -> 'a link [@@unboxed]

let next (Node cell : ('a, [ `Node ]) node) = cell.next
let load_next (Node cell : ('a, [ `Node ]) node) = Atomic.get cell.next
