type cell = { mutable value : int [@caravan.relaxed] }

let allocate value = { value }
let prepare cell value = cell.value <- value
let seal (cell : cell) = cell
let sample cell = cell.value
let unrestricted cell = cell.value
let make_channel (cell : cell) = Atomic.make 1

let receive (channel : int Atomic.t) cell =
  let _ = Atomic.get channel in
  cell.value

let client () =
  let cell = allocate 99 in
  prepare cell 0;
  let cell = seal cell in
  let channel = make_channel cell in
  receive channel cell

let maintain_private (cell : cell) = cell

let publish_at_link initial =
  let cell = { value = 99 } in
  cell.value <- 0;
  let channel = Atomic.make initial in
  let first = Atomic.compare_and_set channel 0 1 in
  if first then
    let first_value = cell.value in
    first_value
  else (
    cell.value <- 2;
    let second = Atomic.compare_and_set channel 1 2 in
    if second then
      let second_value = cell.value in
      second_value
    else -1)
