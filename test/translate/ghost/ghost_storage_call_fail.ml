let identity (cell : int ref) = cell

let make () =
  let cell =
    identity (ref 0)
    (*@ initializes [Ghost.init tag false] *)
  in
  cell
