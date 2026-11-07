type t = int Atomic.t

let make v = Atomic.make v
let get c = Atomic.get c

let diff c =
  let a = Atomic.get c in
  let b = (* 🙂 *) Atomic.get c in
  a - b
