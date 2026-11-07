(* Calls of the interface's raising functions: a raise handled, and one propagated. *)

let pop_or stack default =
  try Treiber_stack.pop_exn stack with Treiber_stack.Empty -> default
(*@ r = pop_or stack default
    requires Treiber_stack.stack stack xs
    ensures match xs with
      | [] -> r === default && Treiber_stack.stack stack []
      | x :: rest -> r === x && Treiber_stack.stack stack rest *)

let pop stack = Treiber_stack.pop_exn stack
(*@ r = pop stack
    requires Treiber_stack.stack stack xs
    ensures match xs with
      | [] -> false
      | x :: rest -> r === x && Treiber_stack.stack stack rest
    raises Treiber_stack.Empty -> xs = [] && Treiber_stack.stack stack [] *)
