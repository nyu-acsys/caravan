type cell = { label : int; mutable count : int [@caravan.frozen] }

let read cell = cell.label
