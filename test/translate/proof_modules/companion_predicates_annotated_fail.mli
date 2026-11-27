module Box : sig
  type t
  (*@ predicate visible (value : t) *)
  (*@ predicate hidden (value : t) *)
end

val client : Box.t -> unit
(*@ client value requires Box.visible value ensures Box.visible value *)
