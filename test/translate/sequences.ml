(* Sequences, a type of specifications only: Raven's Seq, with indexing s.(i), length,
   last, drop, take and ++, and list literals where a sequence is expected. *)

let id (n : int) = n
(*@ r = id n
    ensures forall s : int sequence, t : int sequence.
      length (s ++ t) = length s + length t
    ensures forall s : int sequence. s = [ r ] -> s.(0) = n && last s = n
    ensures forall s : int sequence. s = [ 1; 2; 3 ] -> drop 1 s = [ 2; 3 ] && take 1 s = [ 1 ]
    ensures forall s : int sequence. s = [] -> length s = 0 *)
