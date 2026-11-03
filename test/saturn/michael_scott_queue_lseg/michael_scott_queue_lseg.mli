type 'a t
(** Michael-Scott queue with a List-valued FIFO specification. *)

(*@ invariant is_queue (q : 'a t) *)
(*@ predicate queue (q : 'a t) (xs [@implicit] : 'a list) *)
val create : unit -> 'a t

(*@ q = create () ensures is_queue q && queue q [] *)
val push : 'a t -> 'a -> unit

(*@ atomic push q value requires is_queue q
    atomic requires queue q xs
    atomic ensures queue q (xs @ [value]) *)
val pop_opt : 'a t -> 'a option

(*@ result = atomic pop_opt q requires is_queue q
    atomic requires queue q xs
    atomic ensures match xs with
      | [] -> result === None && queue q []
      | value :: rest -> result === Some value && queue q rest *)
val is_empty : 'a t -> bool
(*@ result = atomic is_empty q requires is_queue q
    atomic requires queue q xs
    atomic ensures queue q xs && result = (xs === []) *)

val of_list : 'a list -> 'a t
(*@ q = of_list list ensures is_queue q && queue q list *)
