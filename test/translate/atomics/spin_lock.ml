(* A spin lock, with logically atomic contracts: acquire takes effect at the
   compare_and_set that succeeds, and release at its write. *)

type t = bool Atomic.t

(*@ predicate is_lock (l : t) (b [@implicit] : bool) = own l b *)

let create () = Atomic.make false
(*@ l = create ()
    ensures is_lock l false *)
(*@ fold is_lock l false *)

let rec acquire l = if not (Atomic.compare_and_set l false true) then acquire l
(*@ atomic acquire l
    atomic requires is_lock l b
    atomic ensures is_lock l true && b = false *)

let release l = Atomic.set l false
(*@ atomic release l
    atomic requires is_lock l true
    atomic ensures is_lock l false *)

(* The same, with the result of compare_and_set named. *)
let rec acquire' l =
  let locked = Atomic.compare_and_set l false true in
  if locked then () else acquire' l
(*@ atomic acquire' l
    atomic requires is_lock l b
    atomic ensures is_lock l true && b = false *)

(* A client holding the lock alone uses the atomic contracts as ordinary ones. *)
let critical () =
  let l = create () in
  acquire l;
  release l;
  acquire l
(*@ critical () *)

(* A compare_and_set that linearizes the function whether it succeeds or not. *)
let try_acquire l = Atomic.compare_and_set l false true
(*@ commit *)
(*@ r = atomic try_acquire l
    atomic requires is_lock l b
    atomic ensures if r then is_lock l true && b = false else is_lock l b && b *)
