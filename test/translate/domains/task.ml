let work cell =
  cell := !cell + 1;
  !cell
(*@ result = work cell
    requires own cell.contents 0
    ensures own cell.contents 1 && result === 1 *)

let pass (domain : int Domain.t) (cell : int ref) = domain
(*@ result = pass domain cell
    requires Job.handle domain cell
    ensures Job.handle result cell *)
