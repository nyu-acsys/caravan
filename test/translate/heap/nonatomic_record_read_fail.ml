type counter = { mutable count : int }

let read (cell : counter) =
  (*@ proof unfold held cell *)
  let result = cell.count in
  (*@ proof fold held cell *)
  result
(*@ result = read cell requires held cell ensures held cell *)
