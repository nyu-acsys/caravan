type cell = { mutable value : int [@caravan.frozen] }

let identity (value : int) = value
(*@ result = identity value ensures result === value *)
