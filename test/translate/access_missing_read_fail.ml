let read (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun read -> 0) *)
(*@ result = read cell
    requires own cell 0
    ensures own cell 0 && result = 0 *)
(*@ manual *)
