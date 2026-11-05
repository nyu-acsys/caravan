val pair : unit -> int Seq.t * int Seq.t
(*@ result = pair ()
    ensures match result with (first, second) -> first === second *)
