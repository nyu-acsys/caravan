let invalid (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.State.scope (fun step () ->
    let result = step () in
    (result, (cell : bool Atomic.t))) *)
(*@ manual *)
(*@ result = invalid cell requires own cell 0 ensures own cell 0 *)
