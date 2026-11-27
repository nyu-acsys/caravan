type cell = { mutable value : int [@caravan.frozen] }

let preserve (cell : cell) = cell
(*@ result = preserve cell
    requires own ~writer:0 cell.value value
    ensures result === cell *)
