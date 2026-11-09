type 'a cell = { mutable value : 'a }

let read (cell : 'a cell) = cell.value
