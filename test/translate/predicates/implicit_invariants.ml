let create (value : int) = Atomic.make value
let read (cell : int Atomic.t) = Atomic.get cell
let change (cell : int Atomic.t) = Atomic.set cell 1
