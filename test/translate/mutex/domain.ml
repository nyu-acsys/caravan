let work () = 1

(*@ result = work () ensures result === 1 *)
let spawn () = Domain.spawn work
(*@ result = spawn () ensures Job.handle result () *)
