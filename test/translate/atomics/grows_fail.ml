type t = int Atomic.t

let create () = Atomic.make 0
(*@ initially { count = 0 } *)
