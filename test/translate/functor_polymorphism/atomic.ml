module type CELL = sig
  val read : 'a Atomic.t -> 'a
  (*@ result = atomic read cell
      atomic requires own cell value
      atomic ensures own cell value && result === value *)
end

module Read (Cell : CELL) = struct
  let read cell = Cell.read cell
  (*@ result = read cell
      requires own cell value
      ensures own cell value && result === value *)
end

module First = Read (Atomic_argument)
module Second = Read (Atomic_argument)

let clients () =
  let integer = Atomic.make 17 in
  let boolean = Atomic.make true in
  assert (First.read integer = 17);
  assert (Second.read boolean);
  assert (Atomic.get integer = 17);
  let value = ref 7 in
  let cell = Atomic.make value in
  let result = First.read cell in
  assert (result == value);
  result := 11;
  assert (!value = 11)
