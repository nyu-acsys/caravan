module Counter = struct
  let read (cell : int Atomic.t) = Atomic.get cell
end
