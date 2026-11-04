type t

(*@ predicate cell (c : t) (v [@implicit] : int) *)

val make : int -> t
(*@ c = make v ensures cell c v *)

val get : t -> int
(*@ r = atomic get c
    atomic requires cell c v
    atomic ensures r = v && cell c v *)

val diff : t -> int
(*@ r = diff c requires cell c v ensures cell c v && r = 0 *)
