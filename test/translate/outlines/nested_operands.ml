let read (cell : int Atomic.t) = Atomic.get cell
let increment value = value + 1
let difference first second = read first - read second
let nested cell = increment (read cell)
