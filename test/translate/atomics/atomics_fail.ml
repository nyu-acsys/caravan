(* A compare_and_set on lists compares physically: equal lists need not be the same. *)
let push a (x : int) =
  let l = Atomic.get a in
  Atomic.compare_and_set a l (x :: l)
(*@ r = push a x
    requires own a l
    ensures own a (x :: l) && r *)

let same (a : int list) b = a == b
(*@ r = same a b
    requires a = b
    ensures r *)

let unowned (a : int Atomic.t) = Atomic.set a 1
let overflow a = Atomic.incr a
(*@ overflow a
    requires own a max_int
    ensures own a (max_int + 1) *)
