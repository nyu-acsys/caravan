let read (cell : int Atomic.t) = Atomic.get cell
(*@ result = atomic read [@atomic] cell
    atomic requires own cell value
    atomic ensures own cell value && result = value *)
