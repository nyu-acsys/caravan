(*@ predicate contents (cell : 'a Atomic.t) (value : 'a) *)

val create : 'a -> 'a Atomic.t
(*@ cell = create value ensures contents cell value *)

val read : 'a Atomic.t -> 'a
(*@ result = atomic read cell
    atomic requires contents cell value
    atomic ensures contents cell value && result === value *)
