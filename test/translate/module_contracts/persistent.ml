module type View = sig
  type t

  (*@ invariant shared (x : t) *)

  val touch : t -> unit
  (*@ touch x requires shared x ensures shared x *)
end

module Checked : View = Persistent_actual

let client x = Checked.touch x
(*@ client x requires Checked.shared x ensures Checked.shared x *)
