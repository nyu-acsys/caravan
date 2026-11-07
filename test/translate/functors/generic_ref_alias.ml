module type Value = sig
  type t
end

module Make (Cell : Value) = struct
  type box = Cell.t ref

  let relay (x : box) = x
  (*@ result = relay x ensures result === x *)
end

module First = Make (Actual.First)
module Second = Make (Actual.Second)

let first (x : Actual.First.t ref) = First.relay x
(*@ result = first x ensures result === x *)

let second (x : Actual.Second.t ref) = Second.relay x
(*@ result = second x ensures result === x *)
