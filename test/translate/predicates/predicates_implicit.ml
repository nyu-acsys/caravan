let create () =
  let value = Atomic.make 7 in
  let cell = Atomic.make value in
  (*@ fold held cell *)
  cell

let get (cell : int Atomic.t Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun read ->
    unfold held cell;
    let value = read () in
    fold held cell value;
    value)
  *)
(*@ manual *)
