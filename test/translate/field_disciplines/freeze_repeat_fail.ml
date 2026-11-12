type cell = { mutable value : int [@caravan.frozen] }

let allocate value = { value }
(*@ result = allocate value
    ensures own ~writer:Ghost.self result.value value *)

let freeze_twice value = allocate value
(*@ Ghost.scope (fun step ->
    let cell = step () in
    Value.freeze cell;
    Value.freeze cell;
    cell) *)
(*@ manual *)
(*@ result = freeze_twice value ensures Value.frozen result value *)
