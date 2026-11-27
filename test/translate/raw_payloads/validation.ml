type 'a cell = { mutable value : 'a [@caravan.relaxed] [@caravan.raw] }

let create value =
  let cell = { value } in
  let head = Atomic.make false in
  (head, cell)

let retire head (cell : 'a cell) = Atomic.set head true

let clear head cell =
  Atomic.set head true;
  cell.value <- Obj.magic ()

let peek head cell =
  let value = cell.value in
  if Atomic.get head then None else Some value

let client value =
  let head, cell = create value in
  let before = peek head cell in
  clear head cell;
  let after = peek head cell in
  (before, after)
