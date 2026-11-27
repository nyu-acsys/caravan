type cell = { mutable value : int [@caravan.frozen] }

let read (cell : cell) = cell.value
(*@ Ghost.frozen_scope (fun load -> let result = load () in result) *)
(*@ manual *)
(*@ result = read cell requires Value.visible Ghost.self cell value
    ensures Value.visible Ghost.self cell value && result === value *)

let bad cell =
  let child = Domain.spawn (fun () -> read cell) in
  Domain.join child
(*@ result = bad cell requires Value.frozen cell value ensures result === value *)
