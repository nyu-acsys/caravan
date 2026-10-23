let read (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.access (fun step ->
    let helper = 0 in
    helper ();
    let result = step () in
    result)
  *)
(*@ manual *)
(*@ result = read cell requires own cell 0 ensures own cell 0 *)
