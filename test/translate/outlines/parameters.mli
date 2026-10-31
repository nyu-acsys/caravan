type t

(*@ predicate cell (c : t) (v [@implicit] : int) *)

val make : int -> t
(*@ c = make v
    ensures cell c v *)

val get : t -> int
(*@ r = atomic get c
    atomic requires cell c v
    atomic ensures r = v && cell c v *)

val twice : t -> int
(*@ r = atomic twice c
    atomic requires cell c v
    atomic ensures cell c v *)
