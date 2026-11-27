type record = { mutable value : int [@caravan.frozen] }

let allocate value = { value }
(*@ cell = allocate value
    ensures own cell.value value && own cell.value value *)
