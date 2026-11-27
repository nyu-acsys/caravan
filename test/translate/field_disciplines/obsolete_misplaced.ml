type t = { mutable counter : int } [@@caravan.history]

let identity (cell : t) = cell
