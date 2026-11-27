let make (cell : int ref) = Mutex.create ()

let client () =
  let cell = ref 0 in
  make cell
