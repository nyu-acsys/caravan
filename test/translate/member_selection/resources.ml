module Checked : sig
  type t
  (*@ predicate owned (cell : t) *)

  val make : unit -> t
  (*@ result = make token ensures owned result *)
end = struct
  type t = { mutable count : int }

  let make () = { count = 0 }
end
