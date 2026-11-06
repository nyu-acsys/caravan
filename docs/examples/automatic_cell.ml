type 'a t = 'a Atomic.t

let create value = Atomic.make value
let read cell = Atomic.get cell

let rec set cell value =
  let before = Atomic.get cell in
  if Atomic.compare_and_set cell before value then () else set cell value
