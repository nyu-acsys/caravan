let protect (mutex : Mutex.t) = Mutex.protect mutex (fun () -> 7)
