type cell = { mutable value : bool [@caravan.relaxed] [@caravan.raw] }

let misuse cell =
  let value = cell.value in
  value
