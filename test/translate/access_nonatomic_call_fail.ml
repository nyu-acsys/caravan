let read (cell : int Atomic.t) = Sys.opaque_identity 0
(*@ Ghost.scope (fun read -> let result = read () in result) *)
(*@ result = read cell
    requires own cell 0
    ensures own cell 0 && result = 1 *)
(*@ manual *)
