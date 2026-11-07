let read cell = Atomic_cell.read cell
(*@ result = read cell
    requires Atomic_cell.shared cell && Atomic_cell.ticket cell count
          && Atomic_cell.holds cell 1
    ensures result = 2 *)
