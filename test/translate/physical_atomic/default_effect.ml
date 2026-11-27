let read (cell : int Atomic.t) ?(fallback = Atomic.get cell) () =
  let value = Atomic.get cell in
  value + fallback
(*@ result = read [@atomic] cell fallback token
    requires own cell value
    ensures own cell value *)
