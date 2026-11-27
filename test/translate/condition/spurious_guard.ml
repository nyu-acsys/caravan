let spurious_guard mutex condition (cell : bool ref) =
  Mutex.lock mutex;
  cell := true;
  Condition.wait condition mutex;
  let awakened = !cell in
  Mutex.unlock mutex;
  awakened
