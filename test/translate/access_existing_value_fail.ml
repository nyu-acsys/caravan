let read (cell : int Atomic.t) =
  let result = Atomic.get cell in
  result
(*@ Ghost.scope (fun read -> let result = read () in result) *)
(*@ result = read cell
    requires own cell 0
    ensures own cell 0 && result = 0 *)
(*@ manual *)
