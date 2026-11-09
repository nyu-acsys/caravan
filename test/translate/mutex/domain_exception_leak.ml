exception Failed

let work (mutex : Mutex.t) =
  Mutex.lock mutex;
  raise Failed
