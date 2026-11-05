type 'a t = 'a Atomic.t

let skip (_ : int t) = ()

let set_unit (cell : unit t) =
  Atomic.set cell ();
  true
