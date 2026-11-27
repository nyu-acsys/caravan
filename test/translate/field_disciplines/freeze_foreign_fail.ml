type cell = { mutable value : int [@caravan.frozen] }

let allocate value = { value }
(*@ result = allocate value
    ensures own ~writer:Ghost.self result.value value *)

let preserve (cell : cell) = cell
(*@ result = preserve cell
    requires own ~writer:writer cell.value value
    ensures own ~writer:writer cell.value value && result === cell *)

let freeze_foreign cell = preserve cell
(*@ Ghost.scope (fun step ->
    let cell = step () in
    Value.freeze cell;
    cell) *)
(*@ manual *)
(*@ result = freeze_foreign cell
    requires own ~writer:writer cell.value value
    ensures Value.frozen result value *)
