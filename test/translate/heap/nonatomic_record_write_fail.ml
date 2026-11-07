type counter = { mutable count : int }

let write (cell : counter) =
  (*@ proof unfold held cell *)
  cell.count <- 0;
  (*@ proof fold held cell *)
  ()
(*@ write cell requires held cell ensures held cell *)
