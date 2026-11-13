module type Cell = sig
  type t = { mutable value : int [@caravan.relaxed] [@caravan.raw] }
end

module Make (C : Cell) = struct
  let read (cell : C.t) = cell.value
end

module Cells = struct
  type t = { mutable value : int [@caravan.relaxed] [@caravan.raw] }
end

module Alias = Cells
module Reader = Make (Alias)
module Again = Make (Cells)

module Fresh () = struct
  type t = { mutable value : bool [@caravan.relaxed] [@caravan.raw] }

  let read (cell : t) = cell.value
end

module First = Fresh ()
module Second = Fresh ()
