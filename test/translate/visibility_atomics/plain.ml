let get (cell : int Atomic.t) = Atomic.get cell
(*@ result = get cell
    requires own cell value
    ensures own cell value && result = value *)
