let invalid (cell : int Atomic.t Atomic.t) =
  Atomic.get
    (Atomic.get
       cell
       (*@ Ghost.State.scope (fun step () ->
      let result = step () in
      (result, result)) *))
(*@ Ghost.State.scope (fun step (saved : bool) ->
    let result = step () in
    (result, ())) *)
(*@ manual *)
(*@ result = invalid cell requires own cell inner && own inner 7 *)
