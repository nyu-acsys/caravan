module type View = sig
  type t

  (*@ invariant shared (x : t) *)
  val touch : t -> unit
  (*@ touch x requires shared x ensures shared x *)
end

module Make (Cell : View) = struct
  let touch x = Cell.touch x
  (*@ touch x requires Cell.shared x ensures Cell.shared x *)
end

module First = Make (Generic_persistent_actual)
module Repeated = Make (Generic_persistent_actual)

let client x =
  First.touch x;
  Repeated.touch x
(*@ client x requires Generic_persistent_actual.shared x ensures Generic_persistent_actual.shared x *)
