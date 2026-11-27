val drain : 'a Treiber_stack.t -> 'a list
(*@ result = drain stack
    requires Treiber_stack.stack stack xs
    ensures Treiber_stack.stack stack [] && result === xs *)

val test : unit -> int * int list
(*@ result = test ()
    ensures match result with count, content -> count = 20 && count = List.length content *)
