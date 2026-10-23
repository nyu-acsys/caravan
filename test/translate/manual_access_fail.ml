let unclosed (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun read ->
    unfold zero cell;
    let result = read () in
    result)
  *)
(*@ manual *)
(*@ result = unclosed cell requires zero cell ensures zero cell *)
