let rec drain stack =
  match Treiber_stack.pop_opt stack with None -> [] | Some value -> value :: drain stack
(*@ result = drain stack
    requires Treiber_stack.stack stack xs
    ensures Treiber_stack.stack stack xs && result === xs *)
