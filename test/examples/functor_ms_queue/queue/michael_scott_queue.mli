(** The Michael-Scott queue, after Saturn's. *)

type 'a t

(*@ invariant is_queue (q : 'a t) *)
(*@ predicate queue (q : 'a t) (xs [@implicit] : 'a sequence) *)

val create : unit -> 'a t
(*@ q = create ()
    ensures is_queue q && queue q [] *)

val push : 'a t -> 'a -> unit
(*@ atomic push q v
    requires is_queue q
    atomic requires queue q xs
    atomic ensures queue q (xs ++ [ v ]) *)

val is_empty : 'a t -> bool
(*@ b = atomic is_empty q
    requires is_queue q
    atomic requires queue q xs
    atomic ensures queue q xs && b = (length xs = 0) *)

val pop_opt : 'a t -> 'a option
(*@ r = atomic pop_opt q
    requires is_queue q
    atomic requires queue q xs
    atomic ensures if length xs = 0 then r = None && queue q xs
      else r === Some xs.(0) && queue q (drop 1 xs) *)

val of_list : 'a list -> 'a t
(*@ q = of_list xs
    ensures is_queue q && queue q (to_sequence xs) *)
