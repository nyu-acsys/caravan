type t = int Atomic.t

let make v = Atomic.make v
let get c = Atomic.get c
let twice c = Atomic.get c + Atomic.get c
