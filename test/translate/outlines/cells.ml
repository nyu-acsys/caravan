type t = int Atomic.t

let make v = Atomic.make v
let get c = Atomic.get c

let twice c =
  let first = Atomic.get c in
  if first > 0 then first else 0

let both c =
  let first = Atomic.get c in
  let second = Atomic.get c in
  if first > second then first else second
