let wrong_mutex (first : Mutex.t) second condition =
  Mutex.lock second;
  Condition.wait condition second;
  Mutex.unlock second
