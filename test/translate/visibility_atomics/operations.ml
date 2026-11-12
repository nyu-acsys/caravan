type unused = { mutable data : int [@caravan.frozen] }

let create value = Atomic.make value
(*@ cell = create value
    ensures own cell value *)

let read_half (cell : int Atomic.t) = Atomic.get cell
(*@ result = read_half cell
    requires own ~fraction:Permission.half cell value
    ensures own ~fraction:Permission.half cell value && result = value *)

let split_read cell =
  let first = read_half cell in
  let second = read_half cell in
  assert (first = second);
  second
(*@ result = split_read cell
    requires own cell value
    ensures own cell value && result = value *)

let failed_half cell = Atomic.compare_and_set cell 1 2
(*@ result = failed_half cell
    requires own ~fraction:Permission.half cell 0
    ensures own ~fraction:Permission.half cell 0 && not result *)

let write (cell : int Atomic.t) value = Atomic.set cell value
(*@ write cell value
    requires own cell previous
    ensures own cell value *)

let exchange (cell : int Atomic.t) value = Atomic.exchange cell value
(*@ result = exchange cell value
    requires own cell previous
    ensures own cell value && result = previous *)

let exact cell = Atomic.compare_and_set cell 0 1
(*@ result = exact cell
    requires own cell 0
    ensures own cell 1 && result *)

let inexact (cell : int list Atomic.t) expected replacement =
  Atomic.compare_and_set cell expected replacement
(*@ result = inexact cell expected replacement
    requires own cell previous
    ensures if result then previous === expected && own cell replacement
            else own cell previous *)

let arithmetic cell =
  Atomic.incr cell;
  Atomic.decr cell;
  Atomic.fetch_and_add cell 2
(*@ result = arithmetic cell
    requires own cell max_int
    ensures own cell (min_int + 1) && result = max_int *)

let client () =
  let cell = create 0 in
  assert (split_read cell = 0);
  assert (exact cell);
  write cell 3;
  assert (exchange cell max_int = 3);
  assert (arithmetic cell = max_int)
(*@ client () *)
