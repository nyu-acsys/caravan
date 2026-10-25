module Cell = Nested_cells.Nested.Other

let read cell = Cell.read cell
(*@ result = read cell ensures result = 1 *)
