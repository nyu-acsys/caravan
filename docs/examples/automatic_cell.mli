type 'a t
(*@ invariant shared (cell : 'a t) *)
(*@ predicate contents (cell : 'a t) (value : 'a) *)

val create : 'a -> 'a t
(*@ cell = create value ensures shared cell && contents cell value *)

val read : 'a t -> 'a
(*@ result = atomic read cell
    requires shared cell
    atomic requires contents cell value
    atomic ensures contents cell value && result === value *)

val set : 'a t -> 'a -> unit
(*@ atomic set cell value
    requires shared cell
    atomic requires contents cell before
    atomic ensures contents cell value *)
