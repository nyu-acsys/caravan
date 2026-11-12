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
(*@ Ghost.frozen_scope (fun load -> let result = load () in result) *)
(*@ manual *)
(*@ result = read cell
    requires Value.visible Ghost.self cell value
    ensures Value.visible Ghost.self cell value && result === value *)

let client value =
  let cell = create value in
  let domain = Domain.spawn (fun () -> read cell) in
  Domain.join domain
(*@ result = client value ensures result === value *)

let factory_client value =
  let domain = Domain.spawn (fun () -> create value) in
  let cell = Domain.join domain in
  read cell
(*@ result = factory_client value ensures result === value *)

exception Failed

let fail (cell : cell) : int = raise Failed
(*@ result = fail cell
    requires Value.visible Ghost.self cell value
    ensures false
    raises Failed -> Value.visible Ghost.self cell value *)

let failed_client value =
  let cell = create value in
  let domain = Domain.spawn (fun () -> fail cell) in
  try Domain.join domain with Failed -> read cell
(*@ result = failed_client value ensures result === value *)

let parent_keeps value =
  let cell = create value in
  let child = Domain.spawn (fun () -> read cell) in
  let first = read cell in
  let second = Domain.join child in
  assert (first = second);
  second
(*@ result = parent_keeps value ensures result === value *)

let read_pair first second =
  let left = read first in
  let right = read second in
  (left, right)
(*@ result = read_pair first second
    requires Value.visible Ghost.self first left && Value.visible Ghost.self second right
    ensures Value.visible Ghost.self first left && Value.visible Ghost.self second right
         && result === (left, right) *)

let pair_client left right =
  let first = create left in
  let second = create right in
  let child = Domain.spawn (fun () -> read_pair first second) in
  assert (read first = left);
  assert (read second = right);
  Domain.join child
(*@ result = pair_client left right ensures result === (left, right) *)

let nested cell =
  let child = Domain.spawn (fun () -> read cell) in
  Domain.join child
(*@ result = nested cell
    requires Value.visible Ghost.self cell value
    ensures Value.visible Ghost.self cell value && result === value *)

let nested_client value =
  let cell = create value in
  let child = Domain.spawn (fun () -> nested cell) in
  Domain.join child
(*@ result = nested_client value ensures result === value *)

let opaque_read (channel : int Atomic.t) = Atomic.get channel
(*@ Ghost.scope (fun get ->
    unfold contents channel value;
    let result = get () in
    fold contents channel value;
    result) *)
(*@ manual *)
(*@ result = opaque_read channel
    requires contents channel value
    ensures contents channel value && result === value *)

let opaque_client channel =
  let child = Domain.spawn (fun () -> opaque_read channel) in
  Domain.join child
(*@ result = opaque_client channel
    requires contents channel value
    ensures contents channel value && result === value *)
