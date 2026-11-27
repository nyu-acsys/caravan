type 'a cell = { mutable value : 'a }

let write cell value = cell.value <- value
(*@ write cell value
    requires own ~fraction:Permission.half cell.value before
    ensures own ~fraction:Permission.half cell.value value *)
