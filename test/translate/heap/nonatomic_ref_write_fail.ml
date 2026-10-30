let write (cell : int ref) =
  (*@ proof unfold held cell *)
  cell := 0;
  (*@ proof fold held cell *)
  ()
(*@ write cell requires held cell ensures held cell *)
