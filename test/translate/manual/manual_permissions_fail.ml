let unowned (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun read -> let result = read () in result) *)
(*@ manual *)
(*@ result = unowned cell requires zero cell ensures zero cell *)
