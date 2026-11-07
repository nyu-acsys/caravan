let replace_with_seven (cell : int Atomic.t) =
  let _ =
    Atomic.get cell
    (*@ Ghost.State.scope (fun step () ->
      unfold contents cell initial;
      let result = step () in
      fold contents cell initial;
      (result, result)) *)
  in
  let _ =
    Atomic.exchange cell 7
    (*@ Ghost.scope (fun step ->
      unfold contents cell initial;
      let result = step () in
      assert (result === initial);
      fold contents cell 7;
      result) *)
  in
  Atomic.get cell
(*@ Ghost.State.scope (fun step (saved : int) ->
  assert (saved === initial);
  unfold contents cell 7;
  let result = step () in
  assert (result === 7);
  fold contents cell 7;
  (result, ())) *)
(*@ manual *)
(*@ result = replace_with_seven cell
    requires contents cell initial
    ensures contents cell 7 && result === 7 *)
