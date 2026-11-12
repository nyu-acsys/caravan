type cell = { mutable value : int [@caravan.frozen] }

let rewrite (channel : int Atomic.t) (cell : cell) value = cell.value <- value
