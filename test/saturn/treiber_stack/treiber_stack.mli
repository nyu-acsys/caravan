(** Treiber's lock-free stack, after Saturn's. *)

type 'a t

(*@ predicate stack (t : 'a t) (xs [@implicit] : 'a list) *)

val create : unit -> 'a t
(*@ t = create ()
    ensures stack t [] *)

val of_list : 'a list -> 'a t
(*@ t = of_list xs
    ensures stack t xs *)

val is_empty : 'a t -> bool
(*@ b = atomic is_empty t
    atomic requires stack t xs
    atomic ensures b = (xs = []) && stack t xs *)

val push : 'a t -> 'a -> unit
(*@ atomic push t v
    atomic requires stack t xs
    atomic ensures stack t (v :: xs) *)

val pop_opt : 'a t -> 'a option
(*@ r = atomic pop_opt t
    atomic requires stack t xs
    atomic ensures match xs with
      | [] -> r = None && stack t []
      | x :: xs' -> r === Some x && stack t xs' *)

val pop_all : 'a t -> 'a list
(*@ r = atomic pop_all t
    atomic requires stack t xs
    atomic ensures r === xs && stack t [] *)
