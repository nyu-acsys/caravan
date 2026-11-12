type cell = { mutable value : int [@caravan.relaxed] }

let create () =
  let cell = { value = 99 } in
  cell.value <- 0;
  cell

let read cell = cell.value

let client () =
  let cell = create () in
  let worker = Domain.spawn (fun () -> read cell) in
  Domain.join worker

let parent_keeps () =
  let cell = create () in
  let worker = Domain.spawn (fun () -> read cell) in
  let first = read cell in
  let second = Domain.join worker in
  assert (first = second);
  second
