type holder = { cell : int Atomic.t }

let inspect { cell } = Atomic.get cell
(*@ Ghost.scope (fun step ->
    let tagged = Ghost.read (Ghost.at marker q.cell) in
    let result = step () in
    assert (result = tagged);
    result) *)
(*@ manual *)
(*@ result = inspect q
    requires own q.cell 7 && own (Ghost.at marker q.cell) 7
    ensures own q.cell 7 && own (Ghost.at marker q.cell) 7 && result = 7 *)
