type 'a boxed = Box of 'a ref

let compare cell =
  let first = Box cell in
  let second = Box cell in
  assert (first == second)
