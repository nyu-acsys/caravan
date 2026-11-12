type cell = { mutable value : int [@caravan.relaxed] }

let read cell = cell.value
(*@ result = read cell
    requires Value.observed cell event value
    ensures result === value *)
