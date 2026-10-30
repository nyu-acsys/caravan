(* A release that leaves the lock taken, against the contract in lock_fail.mli. *)

type t = bool Atomic.t

let create () = Atomic.make false
(*@ fold is_lock l false *)

let rec acquire l = if not (Atomic.compare_and_set l false true) then acquire l
let release l = Atomic.set l true
