(** A shared stack, with bugs in shared_stack_fail.ml. *)

type t

(*@ invariant is_stack (t : t) *)
(*@ predicate stack (t : t) (xs : int list) *)

val create : unit -> t
(*@ t = create ()
    ensures is_stack t && stack t [] *)

val push : t -> int -> unit
(*@ atomic push t v
    requires is_stack t
    atomic requires stack t xs
    atomic ensures stack t (v :: xs) *)

val clear : t -> unit
(*@ clear t
    requires is_stack t *)
