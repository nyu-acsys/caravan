let read (mutex : Mutex.t) (cell : int ref) =
  if Mutex.try_lock mutex then (
    Mutex.unlock mutex;
    0)
  else !cell
