module Worker : sig
  val run : int ref -> unit
  (*@ run cell requires own cell.contents 0 ensures own cell.contents 1 *)
end = struct
  let run (cell : int ref) = cell := 1
end

let pass (domain : unit Domain.t) (cell : int ref) = domain
(*@ result = pass domain cell
    requires Worker.Job.handle domain cell
    ensures Worker.Job.handle result cell *)
