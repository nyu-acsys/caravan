type cell = { mutable value : int [@caravan.frozen] }

let allocate value = { value }
(*@ result = allocate value
    ensures own ~writer:Ghost.self result.value value *)

let read cell = cell.value
(*@ result = read cell
    requires own ~writer:Ghost.self cell.value value
    ensures own ~writer:Ghost.self cell.value value && result === value *)

let read_half cell = cell.value
(*@ result = read_half cell
    requires own ~fraction:Permission.half ~writer:Ghost.self cell.value value
    ensures own ~writer:Ghost.self ~fraction:Permission.half cell.value value
         && result === value *)

let rewrite cell value = cell.value <- value
(*@ rewrite cell value
    requires own ~writer:Ghost.self cell.value previous
    ensures own ~writer:Ghost.self cell.value value *)

let preserve (cell : cell) = cell
(*@ result = preserve cell
    requires own ~writer:writer cell.value value
    ensures own ~writer:writer result.value value && result === cell *)

let clients value =
  let cell = allocate value in
  let cell = preserve cell in
  assert (read_half cell = value);
  assert (read cell = value);
  rewrite cell value;
  read cell
(*@ result = clients value ensures result === value *)

let packed value = allocate value
(*@ Ghost.scope (fun create ->
      let cell = create () in
      pack cell value Ghost.self;
      cell) *)
(*@ manual *)
(*@ result = packed value ensures owned_by result value Ghost.self *)

let unpacked cell = read cell
(*@ Ghost.scope (fun load ->
      unpack cell value Ghost.self;
      let result = load () in
      pack cell value Ghost.self;
      result) *)
(*@ manual *)
(*@ result = unpacked [value : int] cell
    requires owned_by cell value Ghost.self
    ensures owned_by cell value Ghost.self && result === value *)

let packed_client value =
  let cell = packed value in
  unpacked cell
(*@ Ghost.scope (fun invoke ->
      let result = invoke value in
      result) *)
(*@ manual *)
(*@ result = packed_client value ensures result === value *)
