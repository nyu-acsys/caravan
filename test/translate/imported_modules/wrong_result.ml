module Cell = Nested_cells.Nested.Atomic

let read cell = Nested_cells.Nested.Atomic.read cell
(*@ result = read cell
    requires Cell.shared cell && Cell.ticket cell count && Cell.holds cell 1
    ensures Cell.shared cell && Cell.ticket cell count && Cell.holds cell 1 && result = 2 *)
