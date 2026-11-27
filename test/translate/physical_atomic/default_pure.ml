let read (cell : int Atomic.t) ?(offset = 1) () =
  let value = Atomic.get cell in
  value + offset
(*@ result = read [@atomic] cell offset token
    requires own cell value
    ensures own cell value *)
