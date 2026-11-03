let read (cell : 'a Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun step ->
    let token = Read.bind () in
    let alias = Read.bind () in
    assert (token === alias);
    let value = Read.access token cell in
    unfold contents cell value;
    let result = step () in
    fold contents cell value;
    Read.commit alias cell result;
    result) *)
(*@ manual *)
(*@ result = atomic read cell
    atomic requires contents cell value
    atomic ensures contents cell value && result === value *)

let retry (cell : 'a Atomic.t) =
  let _ =
    Atomic.get cell
    (*@ Ghost.State.scope (fun step () ->
      let token = Retry.bind () in
      let value = Retry.access token cell in
      unfold contents cell value;
      let result = step () in
      fold contents cell value;
      Retry.abort token cell;
      (result, token)) *)
  in
  Atomic.get cell
(*@ Ghost.State.scope (fun step (token : 'a Retry.token) ->
    let value = Retry.access token cell in
    unfold contents cell value;
    let result = step () in
    fold contents cell value;
    Retry.commit token cell result;
    (result, ())) *)
(*@ manual *)
(*@ result = atomic retry cell
    atomic requires contents cell value
    atomic ensures contents cell value && result === value *)

let read_known (cell : 'a Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun step ->
    let token = Known.bind () in
    Known.access token cell expected;
    let result = step () in
    Known.commit token cell expected result result;
    result) *)
(*@ Ghost.returns (fun result () -> result) *)
(*@ manual *)
(*@ result, [seen : 'a] = atomic read_known [expected : 'a] cell
    atomic requires own cell expected
    atomic ensures own cell expected && result === seen && seen === expected *)

let both (integer : int Atomic.t) (boolean : bool Atomic.t) =
  (read integer, read boolean, retry integer, retry boolean)
(*@ result = both integer boolean
    requires contents integer 17 && contents boolean true
    ensures contents integer 17 && contents boolean true &&
      result === (17, true, 17, true) *)

let known_both (integer : int Atomic.t) (boolean : bool Atomic.t) =
  let first =
    read_known integer
    (*@ Ghost.scope (fun invoke ->
      let (result, seen) = invoke 17 in
      assert (result === seen);
      result) *)
  in
  let second =
    read_known boolean
    (*@ Ghost.scope (fun invoke ->
      let (result, seen) = invoke true in
      assert (result === seen);
      result) *)
  in
  (first, second)
(*@ manual *)
(*@ result = known_both integer boolean
    requires own integer 17 && own boolean true
    ensures own integer 17 && own boolean true && result === (17, true) *)

let known_unit (cell : unit Atomic.t) = read_known cell
(*@ Ghost.scope (fun invoke ->
    let (result, seen) = invoke () in
    assert (result === seen);
    result) *)
(*@ manual *)
(*@ result = known_unit cell
    requires own cell ()
    ensures own cell () && result === () *)
