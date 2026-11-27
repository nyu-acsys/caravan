type 'a t = { mutable value : 'a }

let make value = { value }
let read cell = cell.value
let write cell value = cell.value <- value
