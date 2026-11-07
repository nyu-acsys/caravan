(* Wrong facts about sequences. *)

let id (n : int) = n
(*@ r = id n
    ensures forall s : int sequence. length s > 0
    ensures forall s : int sequence. s = [ 1; 2 ] -> last s = 1 *)
