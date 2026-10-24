type t = int Atomic.t

let create () = Atomic.make 0
(*@ q = create () ensures valid q *)
(*@ initially { cells = to_sequence [1]; size = 1 } *)
