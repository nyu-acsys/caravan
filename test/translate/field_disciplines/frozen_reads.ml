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
(*@ result = create value ensures Value.visible Ghost.self result value *)

let read (cell : cell) = cell.value
(*@ Ghost.frozen_scope (fun load ->
    let result = load () in
    result) *)
(*@ manual *)
(*@ result = read cell
    requires Value.visible Ghost.self cell value
    ensures Value.visible Ghost.self cell value && result === value *)

let client value =
  let cell = create value in
  assert (read cell = value);
  read cell
(*@ result = client value ensures result === value *)

let forward (cell : cell) = cell
(*@ result = forward cell
    requires Value.visible writer cell value
    ensures Value.visible writer result value *)

let duplicate (cell : cell) = cell
(*@ result = duplicate cell
    requires Value.visible Ghost.self cell value
    ensures Value.visible Ghost.self cell value && Value.frozen result value *)

let read_private (cell : cell) = cell.value
(*@ Ghost.scope (fun load -> let result = load () in result) *)
(*@ manual *)
(*@ result = read_private cell
    requires own ~fraction:Permission.half ~writer:Ghost.self cell.value value
    ensures own ~fraction:Permission.half ~writer:Ghost.self cell.value value
      && result === value *)

type 'a box = { mutable contents : 'a [@caravan.frozen] }

let box item = { contents = item }
(*@ result = box item ensures own ~writer:Ghost.self result.contents item *)

let freeze_box item = box item
(*@ Ghost.scope (fun step -> let cell = step () in Box.freeze cell; cell) *)
(*@ manual *)
(*@ result = freeze_box item ensures Box.visible Ghost.self result item *)

let read_box (cell : 'a box) = cell.contents
(*@ Ghost.frozen_scope (fun load -> let result = load () in result) *)
(*@ manual *)
(*@ result = read_box cell
    requires Box.visible Ghost.self cell item
    ensures Box.visible Ghost.self cell item && result === item *)

let boxes () =
  assert (read_box (freeze_box 42) = 42);
  assert (read_box (freeze_box true))

type node = Empty | Node of { mutable count : int [@caravan.frozen] }

let node count = Node { count }
(*@ result = node count
    ensures match result with
      | Empty -> false
      | Node cell -> own ~writer:Ghost.self cell.count count *)

let freeze_node count = node count
(*@ Ghost.scope (fun step -> let cell = step () in Count.freeze cell; cell) *)
(*@ manual *)
(*@ result = freeze_node count ensures Count.visible Ghost.self result count *)

let read_node = function Empty -> 0 | Node cell -> cell.count
(*@ Ghost.frozen_scope (fun load -> let result = load () in result) *)
(*@ manual *)
(*@ result = read_node node
    requires Count.visible Ghost.self node count
    ensures Count.visible Ghost.self node count && result === count *)

let nodes count = read_node (freeze_node count)
(*@ result = nodes count ensures result === count *)

module type Storage = sig
  type 'a t = { mutable item : 'a [@caravan.frozen] }
end

module Generic (Storage : Storage) = struct
  let allocate item : 'a Storage.t = { item }
  (*@ result = allocate item ensures own ~writer:Ghost.self result.item item *)

  let freeze item = allocate item
  (*@ Ghost.scope (fun step -> let cell = step () in Item.freeze cell; cell) *)
  (*@ manual *)
  (*@ result = freeze item ensures Item.visible Ghost.self result item *)

  let read (cell : 'a Storage.t) = cell.item
  (*@ Ghost.frozen_scope (fun load -> let result = load () in result) *)
  (*@ manual *)
  (*@ result = read cell
      requires Item.visible Ghost.self cell item
      ensures Item.visible Ghost.self cell item && result === item *)
end

module Storage = struct
  type 'a t = { mutable item : 'a [@caravan.frozen] }
end

module Instance = Generic (Storage)

let generic_seal item = Instance.freeze item
(*@ result = generic_seal item ensures ActualItem.visible Ghost.self result item *)

let generic_read (cell : 'a Storage.t) = Instance.read cell
(*@ result = generic_read cell
    requires ActualItem.visible Ghost.self cell item
    ensures ActualItem.visible Ghost.self cell item && result === item *)

let generic_clients () =
  assert (generic_read (generic_seal 17) = 17);
  assert (generic_read (generic_seal true))

let carried_read (cell : cell) = cell.value
(*@ Ghost.State.frozen_scope (fun load () ->
    let result = load () in
    (result, result)) *)
(*@ manual *)
(*@ result = carried_read cell
    requires Value.visible Ghost.self cell value
    ensures Value.visible Ghost.self cell value && result === value *)
