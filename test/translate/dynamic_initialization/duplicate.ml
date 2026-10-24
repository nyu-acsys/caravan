type t = int Atomic.t

let create () =
  let cell = Atomic.make 7 in
  Atomic.make 0
(*@ q = create () ensures valid q *)
(*@ initially { cells = to_sequence [cell; cell]; size = 2 } *)
