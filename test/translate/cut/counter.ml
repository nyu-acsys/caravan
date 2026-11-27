let get (c : int Atomic.t) = Atomic.get c

let set (r : int ref) =
  r := 1;
  r := 2
