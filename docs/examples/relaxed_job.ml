type job = {
  id : int;
  mutable total : int; [@caravan.frozen]
  mutable completed : int; [@caravan.relaxed]
}

let create id total =
  let job = { id; total = 0; completed = -1 } in
  job.total <- total;
  job.completed <- 0;
  job

let workload job = job.total
let sample job = job.completed
let sample_unrestricted job = job.completed
let set_completed job value = job.completed <- value

let finish job =
  let total = workload job in
  set_completed job total

let client total =
  let job = create 7 total in
  let worker = Domain.spawn (fun () -> finish job) in
  let estimate = sample job in
  Domain.join worker;
  assert (0 <= estimate && estimate <= total);
  estimate
