let swap cell replacement =
  let previous = Atomic_cell.read cell in
  Atomic_cell.replace cell replacement;
  previous
(*@ result = swap cell replacement
    requires Atomic_cell.shared cell && Atomic_cell.ticket cell count
          && Atomic_cell.holds cell previous
    ensures Atomic_cell.shared cell && Atomic_cell.ticket cell count
          && Atomic_cell.holds cell replacement && result = previous *)

let fresh value =
  let cell = Atomic_cell.make value in
  let first = Atomic_cell.read cell in
  let second = Atomic_cell.read cell in
  assert (first = second);
  second
(*@ result = fresh value ensures result = value *)

let forget cell =
  Atomic_cell.forget cell;
  Atomic_cell.read cell
(*@ result = forget cell
    requires Atomic_cell.shared cell && Atomic_cell.ticket cell count
          && Atomic_cell.holds cell previous
    ensures Atomic_cell.shared cell && Atomic_cell.ticket cell count
          && Atomic_cell.holds cell result *)

let pair cell = Atomic_cell.read_pair cell
(*@ result = pair cell
    requires Atomic_cell.shared cell && Atomic_cell.ticket cell count
          && Atomic_cell.holds cell 7
    ensures Atomic_cell.shared cell && Atomic_cell.ticket cell count
          && Atomic_cell.holds cell 7 && result = (7, true) *)

let version cell =
  Atomic_cell.observe_version cell 7;
  Atomic_cell.observe_version cell 7
(*@ version cell
    requires Atomic_cell.versioned cell 7
    ensures Atomic_cell.versioned cell 7 *)
