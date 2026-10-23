type node = End | Next of int * node Atomic.t

let create () =
  let cell = Atomic.make 0 in
  (*@ proof
    let initial = 0 in
    fold live cell {value = initial}
  *)
  cell
(*@ manual *)
(*@ result = create () ensures live result *)

let read (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun step ->
    let state = unfold live cell {value} in
    let observed = step () in
    fold live cell {value = state};
    observed)
  *)
(*@ manual *)
(*@ result = read cell requires live cell ensures live cell *)

let nested (outer : int Atomic.t Atomic.t) (inner : int Atomic.t) =
  Atomic.get
    (Atomic.get
       outer
       (*@ Ghost.scope (fun load ->
        unfold indirect outer inner;
        let reference = load () in
        fold indirect outer inner;
        reference)
      *))
(*@ Ghost.scope (fun fetch ->
      let value = unfold live inner {value} in
      let result = fetch () in
      fold live inner {value = value};
      result)
    *)
(*@ manual *)
(*@ result = nested outer inner
    requires indirect outer inner && live inner
    ensures indirect outer inner && live inner *)

let store (cell : int Atomic.t) value = Atomic.set cell value
(*@ Ghost.scope (fun write ->
    let previous = unfold live cell {value} in
    let stored = write () in
    fold live cell {value = value};
    stored)
  *)
(*@ manual *)
(*@ store cell value requires live cell ensures live cell *)

let exchange (cell : int Atomic.t) value = Atomic.exchange cell value
(*@ Ghost.scope (fun swap ->
    let previous = unfold live cell {value} in
    let original = swap () in
    assert (original = previous);
    fold live cell {value = value};
    original)
  *)
(*@ manual *)
(*@ result = exchange cell value requires live cell ensures live cell *)

let create_chain () =
  let limit = Atomic.make End in
  let first = Atomic.make (Next (7, limit)) in
  (*@ proof
    fold segment limit limit [];
    fold segment first limit [7] {next = limit};
    fold chain first limit {value = 7; tail = []}
  *)
  (first, limit)
(*@ manual *)
(*@ result = create_chain ()
    ensures match result with (first, limit) -> chain first limit *)

let read_chain (first : node Atomic.t) (limit : node Atomic.t) = Atomic.get first
(*@ Ghost.scope (fun inspect ->
    let (value, tail) = unfold chain first limit {value; tail} in
    let next = expose_head first limit value tail in
    let observed = inspect () in
    assert (observed = Next (value, next));
    restore_head first limit value tail next;
    fold chain first limit {value = value; tail = tail};
    observed)
  *)
(*@ manual *)
(*@ result = read_chain first limit requires chain first limit ensures chain first limit *)

let same_name (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun observed ->
  let observed = observed () in
  observed)
*)
(*@ manual *)
(*@ result = same_name cell requires own cell 0 ensures own cell 0 && result = 0 *)

let shadow_operation (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun step ->
  let observed = step () in
  let step = 1 in
  assert (step = 1);
  observed)
*)
(*@ manual *)
(*@ result = shadow_operation cell requires own cell 0 ensures own cell 0 && result = 0 *)
