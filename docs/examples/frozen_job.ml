type job = { id : int; mutable total : int [@caravan.frozen] }

let create id total =
  let job = { id; total = 0 } in
  job.total <- total;
  job

let identifier job = job.id
let workload job = job.total

let client total =
  let job = create 7 total in
  let worker = Domain.spawn (fun () -> workload job) in
  let local = workload job in
  let remote = Domain.join worker in
  assert (local = remote);
  remote

let publish (job : job) = Atomic.make 1

let receive (channel : int Atomic.t) job =
  let _ = Atomic.get channel in
  job.total
