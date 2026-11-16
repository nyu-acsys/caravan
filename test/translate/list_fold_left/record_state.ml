type readings = { first : int; second : int; third : int }

let ordered (left : int Atomic.t) (middle : int Atomic.t) (right : int Atomic.t) =
  let _record =
    { first = Atomic.get left; second = Atomic.get middle; third = Atomic.get right }
  in
  Atomic.get left
(*@ result = ordered left middle right
    requires own left 1 && own middle 2 && own right 3
    ensures result = 1 && own left 1 && own middle 2 && own right 3 *)
