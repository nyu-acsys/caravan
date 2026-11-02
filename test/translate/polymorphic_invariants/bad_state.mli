type 'a t

(*@ invariant is_cell (q : 'a t) *)
(*@ predicate cell (q : 'a t) (value : 'a) *)

val create : 'a -> 'a t
(*@ q = create value ensures is_cell q && cell q value *)
