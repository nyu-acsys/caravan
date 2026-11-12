module Alias = Record_shapes

let make_frozen frozen : Record_shapes.frozen = { frozen }

let rewrite_frozen (cell : Record_shapes.frozen) value =
  cell.frozen <- value;
  cell.frozen

let make_box value : 'a Record_shapes.box = { value }
let read_alias (cell : 'a Record_shapes.alias) = cell.value
let read_module_alias (cell : 'a Alias.box) = cell.value
let freeze_alias (cell : 'a Record_shapes.alias) : 'a Record_shapes.alias = cell
let read_frozen (cell : 'a Record_shapes.box) = cell.value
let make_relaxed payload : 'a Record_shapes.cell = { payload }
let read_relaxed (cell : 'a Record_shapes.cell) = cell.payload
let write_relaxed (cell : 'a Record_shapes.cell) payload = cell.payload <- payload
let make_nested item : Record_shapes.Nested.t = { item }
let read_nested (cell : Record_shapes.Nested.t) = cell.item
let make_first item : Record_shapes.First.t = { item }
let make_second item : Record_shapes.Second.t = { item }
let read_first (cell : Record_shapes.First.t) = cell.item
let read_second (cell : Record_shapes.Second.t) = cell.item
let make_mixed next payload : 'a Record_shapes.mixed = { next; count = 0; payload }
let next (cell : 'a Record_shapes.mixed) = cell.next
let load_next (cell : 'a Record_shapes.mixed) = Atomic.get cell.next

let clients value =
  let frozen = make_frozen 0 in
  assert (rewrite_frozen frozen 1 = 1);
  let integer = make_box value in
  assert (read_alias integer = value);
  assert (read_module_alias integer = value);
  let integer = freeze_alias integer in
  assert (read_frozen integer = value);
  let boolean = make_box true in
  assert (read_alias boolean);
  let boolean = freeze_alias boolean in
  assert (read_frozen boolean);
  let relaxed = make_relaxed value in
  assert (read_relaxed relaxed = value);
  let nested = make_nested value in
  assert (read_nested nested = value);
  let first = make_first 4 in
  let second = make_second 5 in
  assert (read_first first = 4);
  assert (read_second second = 5);
  let channel = Atomic.make value in
  let mixed = make_mixed channel value in
  assert (next mixed == channel);
  load_next mixed
