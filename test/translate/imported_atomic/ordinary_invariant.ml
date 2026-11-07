let read cell = Atomic_cell.read cell
(*@ Ghost.scope (fun step ->
      unfold protected cell;
      let result = step () in
      fold protected cell;
      result) *)
(*@ manual *)
(*@ result = read cell
    requires protected cell && Atomic_cell.shared cell
    ensures protected cell && Atomic_cell.shared cell && result = 0 *)
