let work (cell : int ref) = !cell
(*@ Ghost.returns (fun result () -> result) *)
(*@ manual *)
(*@ result, [seen : int] = work [expected : int] cell
    requires own cell.contents expected
    ensures own cell.contents expected && result = seen && seen = expected *)

let launch (cell : int ref) = Domain.spawn (fun () -> work cell)
(*@ domain = launch cell
    requires own cell.contents 7
    ensures Job.handle domain cell 7 *)
