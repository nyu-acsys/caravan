let work () = 1
(*@ result = work () ensures result === 1 *)

let pass (domain : bool Domain.t) = domain
(*@ result = pass domain
    requires Job.handle domain ()
    ensures Job.handle result () *)
