(** A trusted cell of an integer, whose contents an abstract predicate gives. *)

type t

(*@ predicate holds (c : t) (v [@implicit] : int) *)

val make : int -> t
(*@ c = make v
    ensures holds c v *)

val get : t -> int
(*@ r = get c
    requires holds c v
    ensures holds c v && r = v *)

val set : t -> int -> unit
(*@ set c w
    requires holds c v
    ensures holds c w *)
