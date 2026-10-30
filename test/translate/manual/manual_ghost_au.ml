let read_known (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun step ->
    let token = Read.bind () in
    Read.access token cell expected;
    let result = step () in
    Read.commit token cell expected result result;
    result) *)
(*@ Ghost.returns (fun result () -> result) *)
(*@ manual *)
(*@ result, [seen : int] = atomic read_known [expected : int] cell
    atomic requires own cell expected
    atomic ensures own cell expected && result = seen && seen = expected *)

let use_known (cell : int Atomic.t) = read_known cell
(*@ Ghost.scope (fun invoke ->
    let (result, seen) = invoke 7 in
    assert (result = seen);
    result) *)
(*@ manual *)
(*@ result = use_known cell
    requires own cell 7
    ensures own cell 7 && result = 7 *)

let store_known (cell : int Atomic.t) next = Atomic.set cell next
(*@ Ghost.scope (fun step ->
    let token = Store.bind () in
    Store.access token cell next expected;
    let result = step () in
    Store.commit token cell next expected () ();
    result) *)
(*@ Ghost.returns (fun result () -> ()) *)
(*@ manual *)
(*@ result, [marker : unit] = atomic store_known [expected : int] cell next
    atomic requires own cell expected
    atomic ensures own cell next && marker = () *)

let use_store_known (cell : int Atomic.t) = store_known cell 8
(*@ Ghost.scope (fun invoke ->
    let (result, marker) = invoke 7 in
    assert (result = ());
    assert (marker = ());
    result) *)
(*@ manual *)
(*@ result = use_store_known cell
    requires own cell 7
    ensures own cell 8 && result = () *)

let read_via_state (auxiliary : int Atomic.t) (cell : int Atomic.t) =
  let _ =
    Atomic.get auxiliary
    (*@ Ghost.State.scope (fun step () ->
      let token = ReadState.bind () in
      let result = step () in
      (result, (token, ()))) *)
  in
  Atomic.get cell
(*@ Ghost.State.scope (fun step (token, ()) ->
    ReadState.access token auxiliary cell expected;
    let result = step () in
    ReadState.commit token auxiliary cell expected result result;
    (result, result)) *)
(*@ Ghost.returns (fun result seen -> seen) *)
(*@ manual *)
(*@ result, [seen : int] = atomic read_via_state [expected : int]
      auxiliary cell
    requires own auxiliary 0
    ensures own auxiliary 0
    atomic requires own cell expected
    atomic ensures own cell expected && result = seen && seen = expected *)

let use_read_via_state (auxiliary : int Atomic.t) (cell : int Atomic.t) =
  read_via_state auxiliary cell
(*@ Ghost.scope (fun invoke ->
    let (result, seen) = invoke 7 in
    assert (result = seen);
    result) *)
(*@ manual *)
(*@ result = use_read_via_state auxiliary cell
    requires own auxiliary 0 && own cell 7
    ensures own auxiliary 0 && own cell 7 && result = 7 *)
