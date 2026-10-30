let false_claim (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun read ->
    unfold zero cell;
    let result = read () in
    fold zero cell;
    result)
  *)
(*@ manual *)
(*@ result = false_claim cell requires zero cell ensures zero cell && result = 1 *)
