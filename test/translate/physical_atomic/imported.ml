let read (cell : int Atomic.t) = Physical_cell.read cell
(*@ Ghost.scope (fun read ->
    unfold shared cell;
    let result = read () in
    fold shared cell;
    result) *)
(*@ manual *)
(*@ result = read cell requires shared cell ensures shared cell && result = 8 *)
