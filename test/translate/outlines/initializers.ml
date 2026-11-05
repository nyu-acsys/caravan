type t = { cell : int Atomic.t }

let make value = { cell = Atomic.make value }
let zero () = { cell = Atomic.make 0 }
