let ordinary cell = Queue.ordinary cell
(*@ result = ordinary cell
    requires Queue.holds cell value
    ensures Queue.holds cell value && result = value *)

let read_atomic cell = Queue.read_atomic cell
(*@ result = read_atomic cell
    requires Queue.shared cell && Queue.holds cell value
    ensures Queue.shared cell && Queue.holds cell value && result = value *)

let fresh value =
  let cell = Queue.create value in
  Queue.read_atomic cell
(*@ result = fresh value ensures result = value *)

let independent left right =
  let first = Queue.Left.ordinary left in
  let second = Queue.Right.ordinary right in
  (first, second)
(*@ result = independent left right
    requires Queue.Left.holds left x && Queue.Right.holds right y
    ensures Queue.Left.holds left x && Queue.Right.holds right y && result = (x, y) *)

let answer () = Queue.answer ()
(*@ result = answer () ensures result = 42 *)
