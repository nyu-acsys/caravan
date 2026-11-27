type cell = { mutable value : int [@caravan.frozen] }

let read cell = Atomic.get cell
(*@ Ghost.frozen_scope (fun load ->
    let result = load () in
    result) *)
(*@ manual *)
(*@ result = read cell requires own cell value ensures own cell value && result === value *)
