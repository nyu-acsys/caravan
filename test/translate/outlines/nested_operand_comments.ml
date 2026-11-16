let read (cell : int Atomic.t) = Atomic.get cell
(*@ result = read cell
    requires own cell value
    ensures own cell value && result = value *)

let increment value = value + 1
(*@ result = increment value
    requires value < max_int
    ensures result = value + 1 *)

let difference first second =
  read first -
  (read second
   (*@ Ghost.scope (fun read ->
        let result = read () in assert (result = 3); result) *))
(*@ manual *)
(*@ result = difference first second
    requires own first 7 && own second 3
    ensures own first 7 && own second 3 && result = 4 *)

let nested cell =
  increment
    (read
       cell
       (*@ Ghost.scope (fun read ->
        let result = read () in assert (result = 5); result) *))
(*@ manual *)
(*@ result = nested cell
    requires own cell 5
    ensures own cell 5 && result = 6 *)
