(* The automatic lemma applies wherever its trigger occurs. *)
let counted (values : int list) = ()
(*@ counted values
    ensures len values >= 0 *)

(* A quantified precondition applies to the instances of its trigger. *)
let bounded (values : int list) = ()
(*@ bounded values
    requires forall others : int list [len others]. len others <= 5
    ensures len values <= 5 *)
