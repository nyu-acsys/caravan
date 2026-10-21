(** A spin lock, with its specification: an abstract predicate and contracts. *)

type t

(*@ predicate is_lock (l : t) (b : bool) *)

val create : unit -> t
(*@ l = create ()
    ensures is_lock l false *)

val acquire : t -> unit
(*@ atomic acquire l
    atomic requires is_lock l b
    atomic ensures is_lock l true && b = false *)

val release : t -> unit
(*@ atomic release l
    atomic requires is_lock l true
    atomic ensures is_lock l false *)
