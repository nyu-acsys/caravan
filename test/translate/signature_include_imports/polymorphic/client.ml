let integer (value : int) =
  let cell = Queue.create value in
  Queue.read cell
(*@ result = integer value ensures result = value *)

let boolean (value : bool) =
  let cell = Queue.create value in
  Queue.read cell
(*@ result = boolean value ensures result = value *)

let other (value : int) =
  let cell = Queue.Other.create value in
  Queue.Other.read cell
(*@ result = other value ensures result = value *)
