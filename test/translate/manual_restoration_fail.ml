let wrong_restoration (cell : int Atomic.t) = Atomic.set cell 1
(*@ Ghost.scope (fun write ->
    unfold zero cell;
    let result = write () in
    fold zero cell;
    result)
  *)
(*@ manual *)
(*@ wrong_restoration cell requires zero cell ensures zero cell *)
