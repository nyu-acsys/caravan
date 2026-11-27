type t = { locks : Mutex.t array; counts : int array }

let incr s i =
  let m = s.locks.(i) in
  Mutex.lock m;
  s.counts.(i) <- s.counts.(i) + 1;
  Mutex.unlock m

let create n =
  let counts = Array.make n 0 in
  let locks = Array.make n (Mutex.create ()) in
  for i = 0 to n - 1 do
    locks.(i) <- Mutex.create ()
  done;
  { locks; counts }
