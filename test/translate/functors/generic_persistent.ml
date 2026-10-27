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
module Actual_alias = Generic_persistent_actual
module Via_alias = Make (Actual_alias)
module Other = Make (Generic_persistent_other)

let client x =
  First.touch x;
  Repeated.touch x;
  Via_alias.touch x
(*@ client x requires Generic_persistent_actual.shared x ensures Generic_persistent_actual.shared x *)

let other_client x = Other.touch x
(*@ other_client x requires Generic_persistent_other.shared x ensures Generic_persistent_other.shared x *)
