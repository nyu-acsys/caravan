(* The cell's contents after the write is not the one read before it. *)

let bump c =
  let x = Cell.get c in
  Cell.set c (x + 1);
  x
(*@ r = bump c
    requires Cell.holds c v
    ensures Cell.holds c r *)
