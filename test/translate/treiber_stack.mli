(** Treiber's lock-free stack, of integers, after Saturn's. *)

type t

(*@ predicate stack (t : t) (xs : int list) *)

val create : unit -> t
(*@ t = create ()
    ensures stack t [] *)

val of_list : int list -> t
(*@ t = of_list xs
    ensures stack t xs *)

val is_empty : t -> bool
(*@ b = atomic is_empty t
    atomic requires stack t xs
    atomic ensures b = (xs = []) && stack t xs *)

val push : t -> int -> unit
(*@ atomic push t v
    atomic requires stack t xs
    atomic ensures stack t (v :: xs) *)

val pop_opt : t -> int option
(*@ r = atomic pop_opt t
    atomic requires stack t xs
    atomic ensures match xs with
      | [] -> r = None && stack t []
      | x :: xs' -> r = Some x && stack t xs' *)

val pop_all : t -> int list
(*@ r = atomic pop_all t
    atomic requires stack t xs
    atomic ensures r = xs && stack t [] *)
