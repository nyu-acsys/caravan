module type View = sig
  type t

  (*@ invariant shared (x : t) *)
  val touch : t -> unit
  (*@ touch x requires shared x ensures shared x *)
end

module Make (Cell : View) = struct
  type item = { cell : Cell.t }

  let pack cell : item = { cell }
  (*@ result = pack cell ensures result.cell === cell *)

  let touch (item : item) = Cell.touch item.cell
  (*@ touch item requires Cell.shared item.cell ensures Cell.shared item.cell *)
end

module First = Make (Generic_persistent_actual)
module Again = Make (Generic_persistent_actual)
module Other = Make (Generic_persistent_other)

let client cell = Again.touch (First.pack cell)
(*@ client cell requires Generic_persistent_actual.shared cell
    ensures Generic_persistent_actual.shared cell *)

let other_client cell = Other.touch (Other.pack cell)
(*@ other_client cell requires Generic_persistent_other.shared cell
    ensures Generic_persistent_other.shared cell *)
