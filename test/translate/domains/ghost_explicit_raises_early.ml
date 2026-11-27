exception Failed

let work (cell : int ref) fail =
  cell := 1;
  if fail then raise Failed;
  7
(*@ Ghost.returns (fun result () -> result) *)
(*@ manual *)
(*@ result, [seen : int] = work cell fail
    requires own cell.contents 0
    ensures own cell.contents 1 && result = seen && seen = 7
    raises Failed -> own cell.contents 1 *)

let launch (cell : int ref) fail = Domain.spawn (fun () -> work cell fail)
(*@ Ghost.scope (fun invoke ->
    let (domain, seen) = invoke () in
    assert (seen = 7);
    domain) *)
(*@ manual *)
(*@ domain = launch cell fail
    requires own cell.contents 0
    ensures Job.handle domain cell fail *)
