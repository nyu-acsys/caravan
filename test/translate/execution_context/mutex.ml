type fields = {
  mutable frozen : int; [@caravan.frozen]
  mutable relaxed : bool; [@caravan.relaxed]
}

let lock (mutex : Mutex.t) = Mutex.lock mutex
