type t = { locks : Mutex.t array; counts : int array }

let incr s i = s.counts.(i) <- s.counts.(i) + 1
