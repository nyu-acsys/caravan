(* A client of a library with contracts and abstract predicates, Cell's. *)

let swap a b =
  let x = Cell.get a in
  let y = Cell.get b in
  Cell.set a y;
  Cell.set b x
(*@ swap a b
    requires Cell.holds a x && Cell.holds b y
    ensures Cell.holds a y && Cell.holds b x *)

let fresh () = Cell.make 0
(*@ c = fresh ()
    ensures Cell.holds c 0 *)
