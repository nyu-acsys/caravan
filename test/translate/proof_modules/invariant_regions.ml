type t = int Atomic.t

let create () = Atomic.make 0
let get cell = Atomic.get cell
