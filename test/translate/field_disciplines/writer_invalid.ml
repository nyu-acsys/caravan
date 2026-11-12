type cell = { mutable value : int }

let preserve (cell : cell) = cell
(*@ result = preserve cell
    requires own ~writer:Ghost.self cell.value value
    ensures result === cell *)
