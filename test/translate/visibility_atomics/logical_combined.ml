type unused = { mutable frozen : int [@caravan.frozen] }

let read (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun step ->
    let token = Read.bind () in
    bounce token cell;
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

let read_auto (cell : int Atomic.t) = Atomic.get cell
(*@ commit *)
(*@ result = atomic read_auto cell
    atomic requires contents cell value
    atomic ensures contents cell value && result = value *)

let read_client cell =
  let first = read cell in
  let second = read_retry cell in
  let third = read_auto cell in
  assert (first = second);
  assert (second = third);
  third
(*@ result = read_client cell
    requires contents cell value
    ensures contents cell value && result = value *)

let write_client cell value =
  write cell value;
  read_auto cell
(*@ result = write_client cell value
    requires contents cell previous
    ensures contents cell value && result = value *)
