type record = {
  mutable left : int; [@caravan.frozen]
  mutable right : int; [@caravan.frozen]
}

let create left right = { left; right }
(*@ cell = create left right
    ensures own ~writer:Ghost.self cell.left left && own ~writer:Ghost.self cell.right right *)

let read_local value =
  let cell = { left = value; right = value } in
  cell.left
(*@ result = read_local value ensures result === value *)

let rewrite_left cell value =
  cell.left <- value;
  cell.left
(*@ result = rewrite_left cell value
    requires own ~writer:Ghost.self cell.left previous
    ensures own ~writer:Ghost.self cell.left value && result === value *)

let pattern_local value =
  let cell = { left = value; right = value } in
  let { left; _ } = cell in
  left
(*@ result = pattern_local value ensures result === value *)

let relay_left (cell : record) = cell
(*@ result = relay_left cell
    requires own ~writer:Ghost.self cell.left value
    ensures own ~writer:Ghost.self cell.left value && result === cell *)

let split_left (cell : record) = cell

type 'a box = { mutable value : 'a [@caravan.frozen] }

let box value = { value }
(*@ cell = box value ensures own ~writer:Ghost.self cell.value value *)

let clients () =
  let cell = create 10 20 in
  let cell = relay_left cell in
  assert (rewrite_left cell 10 = 10);
  assert (read_local 11 = 11);
  assert (pattern_local 12 = 12);
  cell.right <- 30;
  assert (cell.right = 30);
  let integer = box 7 in
  integer.value <- 9;
  assert (integer.value = 9);
  let boolean = box false in
  boolean.value <- true;
  assert boolean.value

let packed left right = create left right

type node = Node of { mutable value : int [@caravan.frozen] }

let inline_local value =
  let node = Node { value } in
  match node with
  | Node cell ->
      cell.value <- value;
      cell.value
(*@ result = inline_local value ensures result === value *)
