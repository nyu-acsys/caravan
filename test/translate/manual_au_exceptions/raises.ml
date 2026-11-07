exception Empty

let read cell = match Atomic.get cell with None -> raise Empty | Some value -> value
let consume cell = match Atomic.get cell with None -> raise Empty | Some _ -> ()
let delegate cell = read cell
let delegate_unit cell = consume cell
