let ordered (left : int Atomic.t) (middle : int Atomic.t) (right : int Atomic.t) =
  let _tuple = (Atomic.get left, Atomic.get middle, Atomic.get right) in
  Atomic.get left
(*@ result = ordered left middle right
    requires own left 1 && own middle 2 && own right 3
    ensures result = 1 && own left 1 && own middle 2 && own right 3 *)

let discard (_values : int * int * int) = ()

let argument_state (left : int Atomic.t) (middle : int Atomic.t) (right : int Atomic.t) =
  let _ = Atomic.get right in
  let _ = discard (Atomic.get left, Atomic.get middle, Atomic.get right) in
  Atomic.get left
(*@ result = argument_state left middle right
    requires own left 1 && own middle 2 && own right 3
    ensures result = 1 && own left 1 && own middle 2 && own right 3 *)
