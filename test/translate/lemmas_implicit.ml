type projections = { hd : int; tl : bool }

let invoke (cell : int Atomic.t) =
  (*@ lemma observe cell *)
  ()
(*@ invoke cell
    requires own cell 7
    ensures own cell 7 *)
