let make () =
  let cell = Atomic.make 0 in
  let alias =
    cell
    (*@ initializes [Ghost.init tag false] *)
  in
  alias
