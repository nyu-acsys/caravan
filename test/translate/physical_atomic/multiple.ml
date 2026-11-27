let read (cell : int Atomic.t) =
  let first = Atomic.get cell in
  let second = Atomic.get cell in
  first + second
(*@ result = read [@atomic] cell
    requires own cell value
    ensures own cell value && result = value + value *)
