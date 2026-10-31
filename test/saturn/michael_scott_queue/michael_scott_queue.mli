(** The Michael-Scott queue, of booleans, after Saturn's: its creation, pop, and moving
    its tail on. *)

type t

(*@ invariant is_queue (q : t) *)
(*@ predicate queue (q : t) (xs [@implicit] : bool sequence) *)

val create : unit -> t
(*@ q = create ()
    ensures is_queue q && queue q [] *)

val push : t -> bool -> unit
(*@ atomic push q v
    requires is_queue q
    atomic requires queue q xs
    atomic ensures queue q (xs ++ [ v ]) *)

val is_empty : t -> bool
(*@ b = atomic is_empty q
    requires is_queue q
    atomic requires queue q xs
    atomic ensures queue q xs && b = (length xs = 0) *)

val pop_opt : t -> bool option
(*@ r = atomic pop_opt q
    requires is_queue q
    atomic requires queue q xs
    atomic ensures if length xs = 0 then r = None && queue q xs
      else r = Some xs.(0) && queue q (drop 1 xs) *)

val of_list : bool list -> t
(*@ q = of_list xs
    ensures is_queue q && queue q (to_sequence xs) *)
