let read_registered (cell : int Atomic.t) =
  let first =
    Atomic.get cell
    (*@ Ghost.State.scope (fun step () ->
      let result = step () in
      let state =
        if result >= 0 then
          let registration = Ghost.alloc [Ghost.init watched cell] in
          Registered registration
        else Linked result
      in
      (result, state)) *)
  in
  let second =
    Atomic.get cell
    (*@ Ghost.State.scope (fun step (state : registration_state) ->
      let checked =
        match state with
        | Registered registration ->
            let linked = Ghost.read (Ghost.at watched registration) in
            assert (linked == cell)
        | Linked observed -> assert (observed = observed)
      in
      let result = step () in
      (result, state)) *)
  in
  (first, second)
(*@ manual *)
(*@ result = read_registered cell
    requires own cell value
    ensures own cell value && result = (value, value) *)
