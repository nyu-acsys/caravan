type t = bool Atomic.t

(*@ predicate is_lock (l : t) (b : bool) = own l b *)

let release (l : t) = ()
(*@ atomic release l
    atomic requires is_lock l true
    atomic ensures is_lock l false *)
