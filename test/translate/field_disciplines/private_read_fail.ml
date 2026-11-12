type record = { mutable value : int [@caravan.frozen] }

let read (cell : record) = cell.value
(*@ result = read cell
    requires own cell.value value
    ensures own cell.value value && result === value *)
