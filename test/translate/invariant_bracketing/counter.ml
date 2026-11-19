let get (c : int Atomic.t) = Atomic.get c
let observe (c : int Atomic.t) = Atomic.get c
let try_reset (c : int Atomic.t) v = Atomic.compare_and_set c v 0
let get_twice (c : int Atomic.t) = get c + get c
let get_namespace (c : int Atomic.t) = Atomic.get c
