type cell = { channel : int Atomic.t }

let read cell = Atomic.get cell.channel
let write cell value = Atomic.set cell.channel value
let protected_read cell = read cell
