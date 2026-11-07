(** A lock-free stack whose pop raises when it is empty. *)

type 'a t

exception Empty

(*@ predicate stack (t : 'a t) (xs [@implicit] : 'a list) *)

val create : unit -> 'a t
(*@ t = create ()
    ensures stack t [] *)

val push : 'a t -> 'a -> unit
(*@ atomic push t v
    atomic requires stack t xs
    atomic ensures stack t (v :: xs) *)

val pop_exn : 'a t -> 'a
(*@ r = atomic pop_exn t
    atomic requires stack t xs
    atomic ensures match xs with [] -> false | x :: xs' -> r === x && stack t xs'
    atomic raises Empty -> xs = [] && stack t [] *)
