let state_chain (cell : int Atomic.t) =
  let first =
    Atomic.get cell
    (*@ Ghost.State.scope (fun step () ->
      let result = step () in
      (result, result)) *)
  in
  let second =
    Atomic.exchange cell (first + 1)
    (*@ Ghost.State.scope (fun step (known : int) ->
      let result = step () in
      assert (result = known);
      (result, (known, known + 1))) *)
  in
  let third =
    Atomic.get cell
    (*@ Ghost.State.scope (fun step (before, after) ->
      let result = step () in
      assert (result = after);
      (result, ())) *)
  in
  (first, second, third)
(*@ manual *)
(*@ result = state_chain cell
    requires own cell initial && initial < max_int
    ensures own cell (initial + 1) && result = (initial, initial, initial + 1) *)

let branch_state (cell : int Atomic.t) choose =
  let initial =
    Atomic.get cell
    (*@ Ghost.State.scope (fun step () ->
      let result = step () in
      (result, result)) *)
  in
  let _ =
    if choose then Atomic.get cell
      (*@ Ghost.State.scope (fun step (saved : int) ->
        let result = step () in
        assert (result = saved);
        (result, true)) *)
    else Atomic.get cell
    (*@ Ghost.State.scope (fun step (saved : int) ->
        let result = step () in
        assert (result = saved);
        (result, ())) *)
  in
  let final =
    Atomic.get cell
    (*@ Ghost.State.scope (fun step (saved : int) ->
      let result = step () in
      assert (result = saved);
      (result, saved)) *)
  in
  (initial, final)
(*@ manual *)
(*@ result = branch_state cell choose
    requires own cell value
    ensures own cell value && result = (value, value) *)

let nested_rhs (cell : int Atomic.t) =
  let _ =
    Atomic.get cell
    (*@ Ghost.State.scope (fun step () ->
      let result = step () in
      (result, result)) *)
  in
  let _ =
    let _ =
      Atomic.get cell
      (*@ Ghost.State.scope (fun step (saved : int) ->
        let result = step () in
        (result, false)) *)
    in
    Atomic.get cell
    (*@ Ghost.State.scope (fun step (changed : bool) ->
      let result = step () in
      assert (changed = false);
      (result, changed)) *)
  in
  Atomic.get cell
(*@ Ghost.State.scope (fun step (saved : int) ->
    let result = step () in
    assert (result = saved);
    (result, saved)) *)
(*@ manual *)
(*@ result = nested_rhs cell
    requires own cell value
    ensures own cell value && result = value *)

let ordinary_scope (cell : int Atomic.t) =
  let _ =
    Atomic.get cell
    (*@ Ghost.State.scope (fun step () ->
      let result = step () in
      (result, result)) *)
  in
  let _ =
    Atomic.get cell
    (*@ Ghost.scope (fun step ->
      let result = step () in
      result) *)
  in
  Atomic.get cell
(*@ Ghost.State.scope (fun step (saved : int) ->
    let result = step () in
    assert (result = saved);
    (result, saved)) *)
(*@ manual *)
(*@ result = ordinary_scope cell
    requires own cell value
    ensures own cell value && result = value *)

let loop_state (cell : int Atomic.t) count =
  let _ =
    Atomic.get cell
    (*@ Ghost.State.scope (fun step () ->
      let result = step () in
      (result, result)) *)
  in
  for _ = 1 to count do
    (*@ invariant (fun saved -> own cell value && saved = value) *)
    let _ =
      Atomic.get cell
      (*@ Ghost.State.scope (fun step (saved : int) ->
        let result = step () in
        (result, ())) *)
    in
    ()
  done;
  Atomic.get cell
(*@ Ghost.State.scope (fun step (saved : int) ->
    let result = step () in
    assert (result = saved);
    (result, saved)) *)
(*@ manual *)
(*@ result = loop_state cell count
    requires own cell value
    ensures own cell value && result = value *)

let sequence_state (cell : int Atomic.t) =
  Atomic.get cell
  (*@ Ghost.State.scope (fun step () ->
    let result = step () in
    (result, result)) *);
  Atomic.get cell
(*@ Ghost.State.scope (fun step (saved : int) ->
    let result = step () in
    assert (result = saved);
    (result, saved)) *)
(*@ manual *)
(*@ result = sequence_state cell
    requires own cell value
    ensures own cell value && result = value *)

type marker = unit

let unit_alias (cell : int Atomic.t) =
  let _ =
    Atomic.get cell
    (*@ Ghost.State.scope (fun step () ->
      let result = step () in
      (result, (() : marker))) *)
  in
  Atomic.get cell
(*@ Ghost.State.scope (fun step () ->
    let result = step () in
    (result, ())) *)
(*@ manual *)
(*@ result = unit_alias cell requires own cell value
    ensures own cell value && result = value *)
