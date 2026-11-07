type 'a t

(*@ invariant is_cell (q : 'a t) *)
(*@ predicate cell (q : 'a t) (value : 'a * int) *)

val create : 'a -> 'a t
(*@ q = create value ensures is_cell q && cell q (value, max_int + 1) *)

val read : 'a t -> 'a
(*@ result = atomic read q
    requires is_cell q
    atomic requires cell q (value, tag)
    atomic ensures cell q (value, tag) && result === value *)
