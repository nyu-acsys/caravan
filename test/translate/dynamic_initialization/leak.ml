type t = int Atomic.t

let create () = Atomic.make 0
(*@ q = create () ensures valid q *)
(*@ initially let cells = empty_cells () in
  { cells = to_sequence cells; size = 0 } *)
(*@ proof assert (cells === []) *)
