let read cell = Atomic_cell.read cell
(*@ result = read cell
    requires Atomic_cell.shared cell && Atomic_cell.ticket cell count *)
