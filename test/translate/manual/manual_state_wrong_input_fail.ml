let read (cell : int Atomic.t) =
  let _ =
    Atomic.get cell
    (*@ Ghost.State.scope (fun step () ->
      let result = step () in
      (result, result)) *)
  in
  Atomic.get cell
(*@ Ghost.State.scope (fun step (saved : bool) ->
    let result = step () in
    (result, saved)) *)
(*@ manual *)
(*@ result = read cell requires own cell value ensures own cell value && result = value *)
