type t
(** Michael-Scott queue with a List-valued FIFO specification. *)

(*@ invariant is_queue (q : t) *)
(*@ predicate queue (q : t) (xs : int list) *)
val create : unit -> t

(*@ q = create () ensures is_queue q && queue q [] *)
val push : t -> int -> unit

(*@ atomic push q value requires is_queue q
    atomic requires queue q xs
    atomic ensures queue q (xs @ [value]) *)
val pop_opt : t -> int option

(*@ result = atomic pop_opt q requires is_queue q
    atomic requires queue q xs
    atomic ensures match xs with
      | [] -> result = None && queue q []
      | value :: rest -> result = Some value && queue q rest *)
val swing_tail : t -> unit

(*@ swing_tail q requires is_queue q *)
val is_empty : t -> bool
(*@ result = atomic is_empty q requires is_queue q
    atomic requires queue q xs
    atomic ensures queue q xs && result = (xs = []) *)
