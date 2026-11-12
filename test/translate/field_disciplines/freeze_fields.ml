type cell = { mutable value : int [@caravan.frozen] }

let allocate value = { value }
(*@ result = allocate value
    ensures own ~writer:Ghost.self result.value value *)

let create value = allocate value
(*@ Ghost.scope (fun step ->
    let cell = step () in
    Value.freeze cell;
    cell) *)
(*@ manual *)
(*@ cell = create value ensures Value.frozen cell value *)

let duplicate (cell : cell) = cell
(*@ result = duplicate cell
    requires Value.frozen cell value
    ensures Value.frozen cell value && Value.frozen result value *)

type 'a box = { mutable contents : 'a [@caravan.frozen] }

let box value = { contents = value }
(*@ result = box value
    ensures own ~writer:Ghost.self result.contents value *)

let freeze_box value = box value
(*@ Ghost.scope (fun step ->
    let cell = step () in
    Box.freeze cell;
    cell) *)
(*@ manual *)
(*@ result = freeze_box value ensures Box.frozen result value *)

let boxes () =
  let _ = freeze_box 42 in
  let _ = freeze_box true in
  ()

type node = Empty | Node of { mutable count : int [@caravan.frozen] }

let node count = Node { count }
(*@ result = node count
    ensures match result with
      | Empty -> false
      | Node cell -> own ~writer:Ghost.self cell.count count *)

let freeze_node count = node count
(*@ Ghost.scope (fun step ->
    let node = step () in
    Count.freeze node;
    node) *)
(*@ manual *)
(*@ result = freeze_node count ensures Count.frozen result count *)

module type Storage = sig
  type 'a t = { mutable item : 'a [@caravan.frozen] }
end

module Generic (Storage : Storage) = struct
  let allocate item : 'a Storage.t = { item }
  (*@ result = allocate item
      ensures own ~writer:Ghost.self result.item item *)

  let freeze item = allocate item
  (*@ Ghost.scope (fun step ->
      let cell = step () in
      Item.freeze cell;
      cell) *)
  (*@ manual *)
  (*@ result = freeze item ensures Item.frozen result item *)
end

module Storage = struct
  type 'a t = { mutable item : 'a [@caravan.frozen] }
end

module Instance = Generic (Storage)

let generic_seal item = Instance.freeze item
(*@ result = generic_seal item ensures ActualItem.frozen result item *)

let generic_clients () =
  let _ = generic_seal 17 in
  let _ = generic_seal true in
  ()
