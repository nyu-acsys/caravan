type cell = { value : int }

let read (cell : cell) = cell.value
(*@ Ghost.frozen_scope (fun load ->
    let result = load () in
    assert false;
    result) *)
(*@ manual *)
