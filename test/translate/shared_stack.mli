(** Treiber's stack, of integers, shared: [is_stack t] is the structure's invariant, which
    any number of threads can hold, and [stack t xs] a client's exclusive view of its
    contents. *)

type t

(*@ invariant is_stack (t : t) *)
(*@ predicate stack (t : t) (xs : int list) *)

val create : unit -> t
(*@ t = create ()
    ensures is_stack t && stack t [] *)

val is_empty : t -> bool
(*@ b = atomic is_empty t
    requires is_stack t
    atomic requires stack t xs
    atomic ensures b = (xs = []) && stack t xs *)

val push : t -> int -> unit
(*@ atomic push t v
    requires is_stack t
    atomic requires stack t xs
    atomic ensures stack t (v :: xs) *)

val pop_opt : t -> int option
(*@ r = atomic pop_opt t
    requires is_stack t
    atomic requires stack t xs
    atomic ensures match xs with
      | [] -> r = None && stack t []
      | x :: xs' -> r = Some x && stack t xs' *)

val pop_all : t -> int list
(*@ r = atomic pop_all t
    requires is_stack t
    atomic requires stack t xs
    atomic ensures r = xs && stack t [] *)
