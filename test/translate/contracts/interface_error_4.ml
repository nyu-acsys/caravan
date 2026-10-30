type t = bool Atomic.t

(*@ predicate is_lock (l : t) (b : bool) = own l b *)
