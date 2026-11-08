let work (cell : int ref) = cell := !cell + 1
(*@ work cell
    requires own cell.contents n && n < max_int
    ensures own cell.contents (n + 1) *)

let client () =
  let cell = ref 7 in
  let domain = Domain.spawn (fun () -> work cell) in
  Domain.join domain;
  !cell
(*@ result = client () ensures result = 8 *)
