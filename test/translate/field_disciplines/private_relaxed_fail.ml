type t = { mutable counter : int [@caravan.relaxed] }

let read cell = cell.counter
(*@ result = read cell
    requires own cell.counter value
    ensures own cell.counter value && result === value *)
