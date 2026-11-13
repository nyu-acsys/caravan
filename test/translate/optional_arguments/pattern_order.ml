type cell = { mutable value : int }

let later cell ?(token = cell.value <- 1) { value } = value
let earlier { value } cell ?(token = cell.value <- 1) () = value

let interleaved cell ?(first = cell.value <- 1) { value = middle }
    ?(second = cell.value <- 2) { value = last } =
  (middle, last)

let some ?(token = ()) (Some value) = value
let selected ?value:(Some item = Some 42) () = item

let client () =
  let first = { value = 0 } in
  assert (later first first = 1);
  let second = { value = 0 } in
  assert (earlier second second () = 0);
  let third = { value = 0 } in
  assert (interleaved third third third = (1, 2));
  assert (some (Some true));
  assert (selected () = 42);
  assert (selected ~value:(Some 7) () = 7)
