let create value = Atomic.make value
let read cell = Atomic.get cell
let read_again cell = read cell
