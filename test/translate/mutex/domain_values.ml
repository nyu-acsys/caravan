let empty () = []

let integers () : int list =
  let child = Domain.spawn empty in
  Domain.join child

let booleans () : bool list =
  let child = Domain.spawn empty in
  Domain.join child
