let make () =
  let value = ref false in
  let cell =
    Atomic.make 0
    (*@ initializes [Ghost.init watched value] *)
  in
  cell
