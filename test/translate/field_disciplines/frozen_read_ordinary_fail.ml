type cell = { mutable value : int }

let read (cell : cell) = cell.value
(*@ Ghost.frozen_scope (fun load ->
    let result = load () in
    result) *)
(*@ manual *)
(*@ result = read cell requires own cell.value value ensures result === value *)
