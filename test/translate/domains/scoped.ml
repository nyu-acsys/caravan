module Worker = struct
  let run (cell : int ref) = cell := 1
  (*@ run cell
      requires own cell.contents 0
      ensures own cell.contents 1 *)
end

module Alias = Worker

let pass (domain : unit Domain.t) (cell : int ref) = domain
(*@ result = pass domain cell
    requires Alias.Job.handle domain cell
    ensures Worker.Job.handle result cell *)

let client () =
  let cell = ref 0 in
  let domain = Domain.spawn (fun () -> Alias.run cell) in
  let alias = pass domain cell in
  Domain.join alias;
  !cell
(*@ result = client () ensures result === 1 *)
