(* Opened library modules give their predicates and functions unqualified. *)
open Cell

let swap a b =
  let x = get a in
  let y = get b in
  set a y;
  set b x
(*@ swap a b
    requires holds a x && holds b y
    ensures holds a y && holds b x *)

let wrapped (c : t) = Holder.read c
(*@ result = wrapped c requires holds c v ensures holds c v && result = v *)
