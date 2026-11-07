type t = int Atomic.t

let create (cell : int Atomic.t) = Atomic.make 0
(*@ q = create cell ensures valid q *)
(*@ initially { cells = to_sequence [cell]; size = 1 } *)
