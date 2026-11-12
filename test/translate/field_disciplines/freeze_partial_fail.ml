type cell = { mutable value : int [@caravan.frozen] }

let allocate value = { value }
(*@ result = allocate value
    ensures own ~writer:Ghost.self result.value value *)

let preserve_half (cell : cell) = cell
(*@ result = preserve_half cell
    requires own ~fraction:Permission.half ~writer:Ghost.self cell.value value
    ensures own ~fraction:Permission.half ~writer:Ghost.self cell.value value && result === cell *)

let freeze_partial cell = preserve_half cell
(*@ Ghost.scope (fun step ->
    let cell = step () in
    Value.freeze cell;
    cell) *)
(*@ manual *)
(*@ result = freeze_partial cell
    requires own ~fraction:Permission.half ~writer:Ghost.self cell.value value
    ensures Value.frozen result value *)
