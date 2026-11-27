type cell = { mutable value : int [@caravan.frozen] }

let read (cell : cell) = cell.value
(*@ Ghost.frozen_scope (fun load ->
    let result = load () in
    result) *)
(*@ manual *)
(*@ result = read cell
    requires Value.visible writer cell value
    ensures result === value *)
