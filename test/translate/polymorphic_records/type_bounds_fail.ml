type 'a cell = { mutable value : 'a }

let read (cell : 'a cell) = cell.value
(*@ result = read cell
    requires own cell.value 0
    ensures own cell.value 0 && result = 0 *)
