type 'a cell = { mutable value : 'a [@caravan.relaxed] [@caravan.raw] }

let unchecked cell = cell.value

let copied cell =
  let value = cell.value in
  let alias = value in
  alias

let boolean (cell : bool cell) = if cell.value then 1 else 2
let arithmetic (cell : int cell) = cell.value + 1
let aggregate cell = Some cell.value
let identity value = value
let call cell = identity cell.value

let capture cell =
  let value = cell.value in
  let helper () = value in
  helper ()

let destructure (cell : int option cell) = match cell.value with None -> 0 | Some n -> n

let pattern (cell : int option cell) =
  let { value = observed } = cell in
  observed
