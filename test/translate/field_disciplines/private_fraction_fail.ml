type record = { mutable value : int [@caravan.frozen] }

let write cell value = cell.value <- value
(*@ write cell value
    requires own ~fraction:Permission.half cell.value previous
    ensures own ~fraction:Permission.half cell.value value *)
