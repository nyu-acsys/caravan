let work (cell : int ref) = cell := !cell + 1
(*@ work cell
    requires own cell.contents n && n < max_int
    ensures own cell.contents (n + 1) *)
