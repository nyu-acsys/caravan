let read (cell : int Atomic.t) choose =
  let _ =
    if choose then Atomic.get cell
      (*@ Ghost.State.scope (fun step () ->
        let result = step () in
        (result, result)) *)
    else 0
  in
  Atomic.get cell
(*@ Ghost.State.scope (fun step (leaked : int) ->
    let result = step () in
    (result, leaked)) *)
(*@ manual *)
(*@ result = read cell choose
    requires own cell value
    ensures own cell value && result = value *)
