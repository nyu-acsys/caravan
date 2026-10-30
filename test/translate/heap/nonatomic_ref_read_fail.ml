let read (cell : int ref) =
  (*@ proof unfold held cell *)
  let result = !cell in
  (*@ proof fold held cell *)
  result
(*@ result = read cell requires held cell ensures held cell *)
