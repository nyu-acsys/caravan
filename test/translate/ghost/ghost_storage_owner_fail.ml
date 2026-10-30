let make () =
  let cell =
    ref 0
    (*@ initializes [Ghost.init tag false] *)
  in
  cell
