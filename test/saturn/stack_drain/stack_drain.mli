val drain : Treiber_stack.t -> int list
(*@ result = drain stack
    requires Treiber_stack.stack stack xs
    ensures Treiber_stack.stack stack [] && result = xs *)
