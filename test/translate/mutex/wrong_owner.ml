let handoff (mutex : Mutex.t) (cell : int ref) =
  Mutex.unlock mutex;
  Mutex.lock mutex
