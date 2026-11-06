let increment value = value + 1
(*@ result = increment value
    requires value < max_int
    ensures result === value + 1 *)

let increment_cell cell =
  let value = !cell in
  cell := value + 1
(*@ increment_cell cell
    requires own cell.contents value && value < max_int
    ensures own cell.contents (value + 1) *)
