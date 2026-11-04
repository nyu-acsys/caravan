(* A raising call in an atomic function, which does not linearize it in its place. *)
let pop_twice t =
  let _ = pop_exn t in
  pop_exn t
