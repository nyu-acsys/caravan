type 'a cell = { mutable value : 'a }

let write cell value = cell.value <- value
(*@ write cell value
    requires own cell.value before
    ensures own cell.value before *)
