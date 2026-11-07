exception Failed

let work (cell : int ref) fail =
  cell := 1;
  if fail then raise Failed else 7
(*@ result = work cell fail
    requires own cell.contents 0
    ensures own cell.contents 1 && result === 7
    raises Failed -> own cell.contents 1 *)

let pass (domain : int Domain.t) (cell : int ref) (fail : bool) = domain
(*@ result = pass domain cell fail
    requires Job.handle domain cell fail
    ensures Job.handle result cell fail *)
