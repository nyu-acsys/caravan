let release (mutex : Mutex.t) = Mutex.unlock mutex

let client () =
  let mutex = Mutex.create () in
  Mutex.lock mutex;
  let child = Domain.spawn (fun () -> release mutex) in
  Mutex.unlock mutex;
  Domain.join child
