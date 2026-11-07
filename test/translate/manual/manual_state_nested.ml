let nested (cell : int Atomic.t Atomic.t) =
  Atomic.get
    (Atomic.get
       cell
       (*@ Ghost.State.scope (fun step () ->
      let result = step () in
      (result, result)) *))
(*@ Ghost.State.scope (fun step (saved : int Atomic.t) ->
    assert (saved == inner);
    let result = step () in
    assert (result = 7);
    (result, ())) *)
(*@ manual *)
(*@ result = nested cell
    requires own cell inner && own inner 7
    ensures own cell inner && own inner 7 && result = 7 *)

let local_chain (cell : int Atomic.t Atomic.t) =
  let _ =
    Atomic.get cell
    (*@ Ghost.State.scope (fun step () ->
      let result = step () in
      (result, 11)) *)
  in
  let found =
    Atomic.get
      (Atomic.get
         cell
         (*@ Ghost.State.scope (fun step (saved : int) ->
        assert (saved = 11);
        let result = step () in
        (result, (result, true))) *))
    (*@ Ghost.State.scope (fun step (saved, marker) ->
      assert (saved == inner && marker);
      let result = step () in
      (result, false)) *)
    = 7
  in
  let _ =
    Atomic.get cell
    (*@ Ghost.State.scope (fun step (saved : int) ->
      assert (saved = 11);
      let result = step () in
      (result, ())) *)
  in
  found
(*@ manual *)
(*@ result = local_chain cell
    requires own cell inner && own inner 7
    ensures own cell inner && own inner 7 && result *)

let continued_chain (cell : int Atomic.t Atomic.t) =
  let value =
    Atomic.get
      (Atomic.get
         cell
         (*@ Ghost.State.scope (fun step () ->
        let result = step () in
        (result, result)) *))
    (*@ Ghost.State.scope (fun step (saved : int Atomic.t) ->
      assert (saved == inner);
      let result = step () in
      (result, result)) *)
  in
  let _ =
    Atomic.get cell
    (*@ Ghost.State.scope (fun step (saved : int) ->
      assert (saved = value);
      let result = step () in
      (result, ())) *)
  in
  value
(*@ manual *)
(*@ result = continued_chain cell
    requires own cell inner && own inner 7
    ensures own cell inner && own inner 7 && result = 7 *)
