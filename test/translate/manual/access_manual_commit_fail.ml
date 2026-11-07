let read (cell : int Atomic.t) = Atomic.get cell
(*@ commit *)
(*@ result = read cell
    requires own cell 0
    ensures own cell 0 && result = 0 *)
(*@ manual *)
