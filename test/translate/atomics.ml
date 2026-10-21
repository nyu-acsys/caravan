(* Atomics are references, owned as a whole: own a v. *)

let create (n : int) = Atomic.make n
(*@ a = create n
    ensures own a n *)

let swap (a : int Atomic.t) b =
  let x = Atomic.get a in
  Atomic.set a (Atomic.exchange b x)
(*@ swap a b
    requires own a x && own b y
    ensures own a y && own b x *)

let try_bump a =
  let v = Atomic.get a in
  Atomic.compare_and_set a v (v + 1)
(*@ r = try_bump a
    requires own a n && n < max_int
    ensures own a (n + 1) && r *)

let stale a = Atomic.compare_and_set a 1 2
(*@ r = stale a
    requires own a 0
    ensures own a 0 && not r *)

let count a =
  Atomic.incr a;
  Atomic.incr a;
  Atomic.fetch_and_add a 10
(*@ r = count a
    requires own a 0
    ensures own a 12 && r = 2 *)

(* fetch_and_add wraps around, as OCaml's integers do. *)
let wrap a = Atomic.incr a
(*@ wrap a
    requires own a max_int
    ensures own a min_int *)

(* A compare_and_set on lists compares physically, so it may fail on equal lists. *)
let push a (x : int) =
  let l = Atomic.get a in
  if Atomic.compare_and_set a l (x :: l) then 1 else 0
(*@ r = push a x
    requires own a l
    ensures if r = 1 then own a (x :: l) else r = 0 && own a l *)

let empty (a : int list Atomic.t) = Atomic.get a == []
(*@ r = empty a
    requires own a l
    ensures own a l && r = (l = []) *)

type state = Idle | Busy

let claim a = Atomic.compare_and_set a Idle Busy
(*@ r = claim a
    requires own a Idle
    ensures own a Busy && r *)
