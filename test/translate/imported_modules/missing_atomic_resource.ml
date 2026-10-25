module Cell = Nested_cells.Nested.Atomic

let read cell = Cell.read cell
(*@ result = read cell
    requires Cell.shared cell && Cell.ticket cell count *)
