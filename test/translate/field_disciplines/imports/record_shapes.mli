type frozen = { mutable frozen : int [@caravan.frozen] }
type 'a box = { mutable value : 'a [@caravan.frozen] }
type 'a alias = 'a box
type 'a cell = { mutable payload : 'a [@caravan.relaxed] }

type 'a mixed = {
  next : 'a Atomic.t;
  mutable count : int; [@caravan.frozen]
  mutable payload : 'a; [@caravan.relaxed]
}

module Nested : sig
  type t = { mutable item : int [@caravan.relaxed] }
end

module type Template = sig
  type t = { mutable item : int [@caravan.frozen] }
end

module First : Template
module Second : Template
