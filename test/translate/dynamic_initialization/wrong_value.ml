type t = int Atomic.t

let create () =
  let cell = Atomic.make 8 in
  Atomic.make 0
(*@ q = create () ensures valid q *)
(*@ initially let cells = one_cell cell in
  { cells = to_sequence cells; size = 1 } *)
