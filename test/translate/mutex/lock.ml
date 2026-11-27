module Native = Mutex

let lock (mutex : Native.t) = Native.lock mutex
