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

exception Empty

val pop_exn : 'a t -> 'a
(*@ r = atomic pop_exn q
    requires is_queue q
    atomic requires queue q xs
    atomic ensures length xs > 0 && r === xs.(0) && queue q (drop 1 xs)
    atomic raises Empty -> length xs = 0 && queue q xs *)

val peek_opt : 'a t -> 'a option
(*@ r = atomic peek_opt q
    requires is_queue q
    atomic requires queue q xs
    atomic ensures queue q xs && if length xs = 0 then r = None else r === Some xs.(0) *)

val peek_exn : 'a t -> 'a
(*@ r = atomic peek_exn q
    requires is_queue q
    atomic requires queue q xs
    atomic ensures queue q xs && length xs > 0 && r === xs.(0)
    atomic raises Empty -> length xs = 0 && queue q xs *)

val drop_exn : 'a t -> unit
(*@ atomic drop_exn q
    requires is_queue q
    atomic requires queue q xs
    atomic ensures length xs > 0 && queue q (drop 1 xs)
    atomic raises Empty -> length xs = 0 && queue q xs *)

val pop_opt : 'a t -> 'a option
(*@ r = atomic pop_opt q
    requires is_queue q
    atomic requires queue q xs
    atomic ensures if length xs = 0 then r = None && queue q xs
      else r === Some xs.(0) && queue q (drop 1 xs) *)

val of_list : 'a list -> 'a t
(*@ q = of_list xs
    ensures is_queue q && queue q (to_sequence xs) *)
