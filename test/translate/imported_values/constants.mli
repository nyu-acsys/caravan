type 'a t

(*@ invariant stable (value : 'a t) *)

val empty : 'a t
(*@ result = empty
    ensures stable result *)

val zero : int
(*@ result = zero
    ensures result = 0 *)

val token : unit
(*@ result = token
    ensures result = () *)
