type cell = { left : int; right : int; mutable count : int [@caravan.frozen] }

let read cell = cell.right
(*@ result = read cell
    requires own cell.left value
    ensures own cell.left value && result === value *)
