type node = End | Next of int

let inspect item =
  match item with
  | End -> 0
  | Next value ->
      let cell = Atomic.make value in
      Atomic.get cell
(*@ Ghost.scope (fun read ->
        let observed = read () in
        assert (observed = value);
        observed) *)
(*@ manual *)
