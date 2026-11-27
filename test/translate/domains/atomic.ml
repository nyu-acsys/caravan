let work (cell : int Atomic.t) = Atomic.get cell
(*@ result = work cell
    atomic requires own cell 0
    atomic ensures own cell 0 && result === 0 *)
