type node = { mutable counter : int [@caravan.frozen] }

type (_, _) queue_node =
  | Null : ('a, [ `Null ]) queue_node
  | Node : {
      mutable counter : int; [@caravan.frozen]
      mutable payload : 'a;
    }
      -> ('a, [ `Node ]) queue_node

module Flags = struct
  type t = { mutable value : bool [@caravan.relaxed] }
end

let read_counter (n : node) = n.counter
