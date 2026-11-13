type 'a cell = { mutable value : 'a [@caravan.relaxed] [@caravan.raw] }

let allocate value = { value }
let clear cell = cell.value <- Obj.magic ()
let load cell = cell.value

let copied cell =
  let value = cell.value in
  let copy = value in
  copy

let empty () : bool cell = { value = Obj.magic () }
let shadow (cell : bool cell) = cell.value

let read_option (cell : int option cell) =
  let value = cell.value in
  match value with None -> 0 | Some n -> n

let checked_capture cell =
  let value = cell.value in
  let helper () = value in
  helper ()

let keep value = value

let checked_call cell =
  let value = cell.value in
  keep value
