let increment (value : int) = value + 1
let read (cell : int Atomic.t) = increment 0
(*@ Ghost.access (fun read -> let result = read () in result) *)
(*@ result = read cell
    requires own cell 0
    ensures own cell 0 && result = 1 *)
(*@ manual *)
