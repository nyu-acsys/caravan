type cell = { mutable value : int [@caravan.frozen] }

let allocate () = { value = 7 }
let create () = allocate ()
let read cell = cell.value
let read_shared cell = read cell
let client () = read_shared (create ())
