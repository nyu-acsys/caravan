type t = bool Atomic.t

(*@ predicate is_lock (l : t) (b : bool) = own l b *)

(* Whether the lock is taken after the first compare_and_set depends on its result. *)
let acquire_twice l =
  let _ = Atomic.compare_and_set l false true in
  let _ = Atomic.compare_and_set l false true in
  ()
(*@ atomic acquire_twice l
    atomic requires is_lock l b
    atomic ensures is_lock l true *)
