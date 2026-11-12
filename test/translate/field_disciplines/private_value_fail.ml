type record = { mutable value : int [@caravan.frozen] }

let allocate value = { value }
(*@ cell = allocate value ensures own cell.value (value + 1) *)
