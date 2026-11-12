type cell = { mutable value : int [@caravan.frozen] }

let read (cell : cell) = cell.value
(*@ result = read cell
    requires own ~writer:writer cell.value value
    ensures own ~writer:writer cell.value value && result === value *)
