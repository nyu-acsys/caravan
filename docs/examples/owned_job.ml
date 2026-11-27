type job = { id : int; mutable work : int }

let create id work = { id; work }
let prepare job work = job.work <- work
let inspect job = job.work

let client () =
  let job = create 7 0 in
  prepare job 42;
  let worker = Domain.spawn (fun () -> inspect job) in
  Domain.join worker
