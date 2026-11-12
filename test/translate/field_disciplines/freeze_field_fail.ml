type cell = {
  mutable left : int; [@caravan.frozen]
  mutable right : int; [@caravan.frozen]
}

let allocate left right = { left; right }
(*@ result = allocate left right
    ensures own ~writer:Ghost.self result.left left &&
            own ~writer:Ghost.self result.right right *)

let freeze_left left right = allocate left right
(*@ Ghost.scope (fun step ->
    let cell = step () in
    Left.freeze cell;
    cell) *)
(*@ manual *)
(*@ result = freeze_left left right ensures Right.frozen result right *)
