type choice = Left of int | Right of int

let inspect choice =
  match choice with
  | Left left ->
      let cell = Atomic.make left in
      Atomic.get cell
  | Right right ->
      let cell = Atomic.make right in
      Atomic.get cell
(*@ Ghost.scope (fun step ->
        let result = step () in
        assert (result = left);
        result) *)
(*@ manual *)
