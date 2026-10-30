let read (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun step ->
    let token = Read.bind () in
    let value = Read.access token cell in
    unfold contents cell value;
    let result = step () in
    fold contents cell value;
    Read.commit token cell result;
    result)
*)
(*@ manual *)
(*@ result = atomic read cell
    atomic requires contents cell value
    atomic ensures contents cell value && result = value *)

let read_alias (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun step ->
    let token = ReadAlias.bind () in
    let alias = ReadAlias.bind () in
    assert (token = alias);
    let value = ReadAlias.access token cell in
    unfold contents cell value;
    let result = step () in
    fold contents cell value;
    ReadAlias.commit alias cell result;
    result)
*)
(*@ manual *)
(*@ result = atomic read_alias cell
    atomic requires contents cell value
    atomic ensures contents cell value && result = value *)

let read_retry (cell : int Atomic.t) =
  let _ =
    Atomic.get cell
    (*@ Ghost.scope (fun step ->
        let token = ReadRetry.bind () in
        let value = ReadRetry.access token cell in
        unfold contents cell value;
        let result = step () in
        fold contents cell value;
        ReadRetry.abort token cell;
        result)
    *)
  in
  Atomic.get cell
(*@ Ghost.scope (fun step ->
      let token = ReadRetry.bind () in
      let value = ReadRetry.access token cell in
      unfold contents cell value;
      let result = step () in
      fold contents cell value;
      ReadRetry.commit token cell result;
      result)
  *)
(*@ manual *)
(*@ result = atomic read_retry cell
    atomic requires contents cell value
    atomic ensures contents cell value && result = value *)

let write (cell : int Atomic.t) value = Atomic.set cell value
(*@ Ghost.scope (fun step ->
    let token = Write.bind () in
    let previous = Write.access token cell value in
    unfold contents cell previous;
    let result = step () in
    fold contents cell value;
    Write.commit token cell value ();
    result)
*)
(*@ manual *)
(*@ atomic write cell value
    atomic requires contents cell previous
    atomic ensures contents cell value *)

let read_pair (cell : int Atomic.t) (expected : int) = Atomic.get cell
(*@ Ghost.scope (fun step ->
    let token = ReadPair.bind () in
    let (previous, tag) = ReadPair.access token cell expected in
    unfold contents cell previous;
    unfold tagged tag;
    let result = step () in
    fold contents cell previous;
    fold tagged tag;
    ReadPair.commit token cell expected result;
    result)
*)
(*@ manual *)
(*@ result = atomic read_pair cell expected
    atomic requires contents cell previous && tagged tag
    atomic ensures contents cell previous && tagged tag && result = previous *)

let constant () = 0
(*@ proof
  let token = Constant.bind () in
  Constant.access token ();
  Constant.commit token () result
*)
(*@ manual *)
(*@ result = atomic constant () atomic ensures result = 0 *)

let read_tuple (cell : int Atomic.t) =
  ( Atomic.get cell
    (*@ Ghost.scope (fun step ->
      let token = ReadTuple.bind () in
      let value = ReadTuple.access token cell in
      unfold contents cell value;
      let observed = step () in
      fold contents cell value;
      ReadTuple.commit token cell (observed, 0);
      observed)
    *),
    0 )
(*@ manual *)
(*@ result = atomic read_tuple cell
    atomic requires contents cell value
    atomic ensures contents cell value && result = (value, 0) *)
