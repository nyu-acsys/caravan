let read (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.access (fun read ->
        if true then let result = read () in result else 0) *)
(*@ result = read cell
    requires own cell 0
    ensures own cell 0 && result = 0 *)
(*@ manual *)
