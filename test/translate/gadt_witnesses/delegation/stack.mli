type 'a t

(*@ predicate stack (t : 'a t) (xs [@implicit] : 'a list) *)

val create : unit -> 'a t
(*@ t = create ()
    ensures stack t [] *)

val pop_opt : 'a t -> 'a option
(*@ r = atomic pop_opt t
    atomic requires stack t xs
    atomic ensures match xs with [] -> r = None && stack t [] | x :: xs' -> r === Some x && stack t xs' *)
