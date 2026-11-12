type cell = { mutable value : int [@caravan.frozen] }

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

let acquire_then_rewrite (channel : int Atomic.t) (cell : cell) value =
  let _ = Atomic.get channel in
  cell.value <- value;
  cell.value
