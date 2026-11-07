module type View = sig
  type t

  (*@ invariant versioned (x : t) (version : int) *)
  val touch_version : t -> int -> unit
  (*@ touch_version x version requires versioned x version ensures versioned x version *)
end

module Make (Cell : View) = struct
  let touch x version = Cell.touch_version x version
  (*@ touch x version requires Cell.versioned x version ensures Cell.versioned x version *)
end

module First = Make (Generic_persistent_actual)
module Repeated = Make (Generic_persistent_actual)

let client x =
  First.touch x 42;
  Repeated.touch x 42
(*@ client x requires Generic_persistent_actual.versioned x 42 ensures Generic_persistent_actual.versioned x 42 *)
