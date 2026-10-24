type t = int Atomic.t

let empty () = Atomic.make 0
(*@ initially
  let cells = empty_cells () in
  { cells = to_sequence cells; size = 0 } *)

let singleton () =
  let cell = Atomic.make 7 in
  Atomic.make 0
(*@ initially
  let cell = one_cell cell in
  { cells = to_sequence cell; size = 1 } *)

let pair () =
  let first = Atomic.make 7 in
  let second = Atomic.make 7 in
  Atomic.make 0
(*@ initially
  let (cells, size) = two_cells first second in
  let cells = keep_cells cells in
  { cells = to_sequence cells; size = size } *)
