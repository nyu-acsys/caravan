(* Raising calls in an atomic function, the second after the first linearized it. *)
let pop_twice t =
  let _ = pop_exn t in
  pop_exn t
