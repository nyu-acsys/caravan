(* Adapted from Saturn's doc/motivation.md; see README.md. *)

let rec drain stack =
  match Treiber_stack.pop_opt stack with None -> [] | Some value -> value :: drain stack
