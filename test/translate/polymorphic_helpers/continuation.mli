type 'a t

(*@ invariant is_cell (q : 'a t) *)
(*@ predicate cell (q : 'a t) (value : 'a) *)

val create : 'a -> 'a t
(*@ q = create value ensures is_cell q && cell q value *)

val read : 'a t -> 'a
(*@ result = atomic read q
    requires is_cell q
    atomic requires cell q value
    atomic ensures cell q value && result === value *)

val set : 'a t -> 'a -> unit
(*@ atomic set q value
    requires is_cell q
    atomic requires cell q before
    atomic ensures cell q value *)

val set_right : 'a t -> 'b t -> 'b -> unit
(*@ atomic set_right left right value
    requires is_cell left && is_cell right
    atomic requires cell left kept && cell right before
    atomic ensures cell left kept && cell right value *)

val mixed : unit -> int * bool
(*@ result = mixed () ensures result === (23, false) *)
