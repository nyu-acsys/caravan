type cell = { next : int Atomic.t; mutable count : int [@caravan.frozen] }

let read cell target =
  let _ = cell.next in
  target.count
