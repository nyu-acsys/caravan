(** The Michael-Scott queue, of integers, after Saturn's: its creation and pop. *)

type t

(*@ predicate is_queue (q : t) [@persistent] *)
(*@ predicate queue (q : t) (xs : int sequence) *)

val create : unit -> t
(*@ q = create ()
    ensures is_queue q && queue q [] *)

val pop_opt : t -> int option
(*@ r = atomic pop_opt q
    requires is_queue q
    atomic requires queue q xs
    atomic ensures if length xs = 0 then r = None && queue q xs
      else r = Some xs.(0) && queue q (drop 1 xs) *)
