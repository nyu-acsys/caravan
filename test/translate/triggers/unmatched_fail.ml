(* The quantified precondition is never instantiated: no term matches its trigger. *)
let bounded (values : int list) = ()
(*@ bounded values
    requires forall others : int list [doubled others]. len others <= 5
    ensures len values <= 5 *)
