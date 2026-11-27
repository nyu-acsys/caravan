type queue = { head : int Atomic.t }

let retain (head : int Atomic.t) = head

let choose ?(token = ()) ({ head } as queue) =
  let _ = token in
  let _ = queue in
  retain head

let client () =
  let head = Atomic.make 7 in
  assert (choose { head } == head)
