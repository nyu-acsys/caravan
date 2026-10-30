type t = bool Atomic.t

(*@ predicate is_lock (l : t) (b : bool) = own l b *)

let try_acquire l = Atomic.compare_and_set l false true
(*@ returning true -> commit *)
(*@ r = atomic try_acquire l
    atomic requires is_lock l b
    atomic ensures if r then is_lock l true && b = false else is_lock l b && b *)
