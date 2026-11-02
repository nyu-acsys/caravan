val drain : 'a Treiber_stack.t -> 'a list
(*@ result = drain stack
    requires Treiber_stack.stack stack xs
    ensures Treiber_stack.stack stack [] && result === xs *)
