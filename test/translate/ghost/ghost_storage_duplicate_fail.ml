let make () =
  let cell =
    Atomic.make 0
    (*@ initializes [Ghost.init tag false; Ghost.init tag true] *)
  in
  cell
