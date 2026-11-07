let make value = ref value
(*@ cell = make value ensures own cell.contents value *)

let read cell = !cell
(*@ result = read cell
    requires own cell.contents value
    ensures own cell.contents value && result === value *)

let write cell value = cell := value
(*@ write cell value
    requires own cell.contents before
    ensures own cell.contents value *)

let make_atomic value = Atomic.make value
(*@ cell = make_atomic value ensures own cell value *)

let read_atomic cell = Atomic.get cell
(*@ result = read_atomic cell
    requires own cell value
    ensures own cell value && result === value *)

let exchange cell value = Atomic.exchange cell value
(*@ result = exchange cell value
    requires own cell before
    ensures own cell value && result === before *)

let integers () =
  let cell = make 17 in
  write cell 42;
  let value = read cell in
  assert (value = 42);
  let atomic = make_atomic 17 in
  let before = exchange atomic 42 in
  assert (before = 17);
  assert (read_atomic atomic = 42)

let booleans () =
  let cell = make false in
  write cell true;
  assert (read cell);
  let atomic = make_atomic false in
  let before = exchange atomic true in
  assert (not before);
  assert (read_atomic atomic)
