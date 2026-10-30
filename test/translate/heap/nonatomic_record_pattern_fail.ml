type counter = { mutable count : int }

let read (cell : counter) =
  (*@ proof unfold held cell *)
  let { count } = cell in
  (*@ proof fold held cell *)
  count
(*@ result = read cell requires held cell ensures held cell *)
