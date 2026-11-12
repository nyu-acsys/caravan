type unused = { mutable frozen : int [@caravan.frozen] }

let read_twice cell =
  let first = Imported_cell.read cell in
  let second = Imported_cell.read cell in
  assert (first = second);
  second
(*@ result = read_twice cell
    requires Imported_cell.holds cell value
    ensures Imported_cell.holds cell value && result === value *)
