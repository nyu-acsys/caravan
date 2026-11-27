let client () =
  let mutex = Mutex.create () in
  Mutex.lock mutex;
  Mutex.unlock mutex
