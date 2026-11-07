let read (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun read ->
        let result = read () in
        let result = 0 in
        result) *)
(*@ result = read cell
    requires own cell 0
    ensures own cell 0 && result = 0 *)
(*@ manual *)
