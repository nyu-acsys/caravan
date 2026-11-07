let create value = Atomic.make value
let read cell = Atomic.get cell
