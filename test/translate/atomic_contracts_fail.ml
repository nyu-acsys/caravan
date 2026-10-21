(* Atomic contracts that the code does not meet. *)

type t = bool Atomic.t

(*@ predicate is_lock (l : t) (b : bool) = own l b *)

(* The write takes effect, but leaves the lock taken. *)
let release l = Atomic.set l true
(*@ atomic release l
    atomic requires is_lock l true
    atomic ensures is_lock l false *)

(* A successful compare_and_set from true does not acquire the lock. *)
let rec acquire l = if not (Atomic.compare_and_set l true true) then acquire l
(*@ atomic acquire l
    atomic requires is_lock l b
    atomic ensures is_lock l true && b = false *)
