exception Failed

let cleanup (mutex : Mutex.t) (cell : int ref) fail =
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

let client fail =
  let cell = ref 0 in
  let mutex = Mutex.create () in
  try
    cleanup mutex cell fail;
    true
  with Failed -> false
