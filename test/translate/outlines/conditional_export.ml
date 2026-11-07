type t = int Atomic.t

let make v = Atomic.make v

let diff c =
  let d = c in
  let a = if d == c then Atomic.get d else 0 in
  let b = Atomic.get c in
  a - b
