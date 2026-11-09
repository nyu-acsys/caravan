exception Failed

let work (mutex : Mutex.t) (cell : int ref) fail =
  Mutex.lock mutex;
  let error =
    try
      cell := 1;
      if fail then raise Failed;
      false
    with Failed -> true
  in
  Mutex.unlock mutex;
  if error then raise Failed

let launch mutex cell fail =
  let child = Domain.spawn (fun () -> work mutex cell fail) in
  try Domain.join child with Failed -> ()

let client fail =
  let cell = ref 0 in
  let mutex = Mutex.create () in
  let first = Domain.spawn (fun () -> work mutex cell false) in
  let second = Domain.spawn (fun () -> work mutex cell fail) in
  (try Domain.join first with Failed -> ());
  try Domain.join second with Failed -> ()

let parent_held () =
  let cell = ref 0 in
  let mutex = Mutex.create () in
  Mutex.lock mutex;
  let child = Domain.spawn (fun () -> work mutex cell false) in
  Mutex.unlock mutex;
  try Domain.join child with Failed -> ()

let nested fail =
  let cell = ref 0 in
  let mutex = Mutex.create () in
  let child = Domain.spawn (fun () -> launch mutex cell fail) in
  Domain.join child
