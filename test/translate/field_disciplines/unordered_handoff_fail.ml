type cell = { mutable value : int [@caravan.frozen] }

let overwrite (channel : int Atomic.t) (target : cell) (spare : cell) =
  let _ = Atomic.get channel in
  target.value <- 1;
  target.value
