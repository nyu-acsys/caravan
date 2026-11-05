let pop stack = Treiber_stack.pop_exn stack
(*@ r = pop stack
    requires Treiber_stack.stack stack xs
    ensures match xs with
      | [] -> false
      | x :: rest -> r === x && Treiber_stack.stack stack rest *)
