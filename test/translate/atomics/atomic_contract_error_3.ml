type t = bool Atomic.t

(*@ predicate is_lock (l : t) (b : bool) = own l b *)

let acquire l =
  while not (Atomic.compare_and_set l false true) do
    ()
  done
(*@ atomic acquire l
    atomic requires is_lock l b
    atomic ensures is_lock l true && b = false *)
