type cell = { mutable value : int [@caravan.frozen] }

let preserve (cell : cell) = cell
(*@ result = preserve cell
    requires own cell.value value
    ensures own ~writer:Ghost.self cell.value value && result === cell *)
