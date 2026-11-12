type cell = { mutable value : int [@caravan.relaxed] }

let read cell = cell.value
(*@ result = read cell
    requires Value.state cell current writes
    ensures Value.state cell current writes && result === current *)
