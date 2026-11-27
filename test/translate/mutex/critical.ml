let put (mutex : Mutex.t) (cell : int ref) =
  Mutex.lock mutex;
  cell := 1;
  Mutex.unlock mutex

let repeat (mutex : Mutex.t) (cell : int ref) =
  for i = 0 to 2 do
    put mutex cell
  done

let try_put (mutex : Mutex.t) (cell : int ref) =
  if Mutex.try_lock mutex then (
    cell := 1;
    Mutex.unlock mutex;
    true)
  else false

let self_try (mutex : Mutex.t) (cell : int ref) =
  Mutex.lock mutex;
  let success = Mutex.try_lock mutex in
  assert (not success);
  Mutex.unlock mutex

let client () =
  let cell = ref 0 in
  let mutex = Mutex.create () in
  put mutex cell;
  repeat mutex cell;
  self_try mutex cell;
  try_put mutex cell

let held_loop (mutex : Mutex.t) (cell : int ref) =
  Mutex.lock mutex;
  for i = 0 to 2 do
    cell := 1
  done;
  Mutex.unlock mutex
