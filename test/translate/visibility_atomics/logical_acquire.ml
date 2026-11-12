type cell = { mutable value : int [@caravan.frozen] }

let receive (channel : int Atomic.t) (payload : cell) =
  let _ =
    Atomic.get channel
    (*@ Ghost.acquire_scope (fun acquire ->
      let token = Receive.bind () in
      let flag = Receive.access token channel payload published value in
      unfold contents channel published flag;
      let result = acquire published in
      fold contents channel published flag;
      Receive.abort token channel payload published value;
      Value.observe payload published;
      result) *)
  in
  let _ =
    payload.value
    (*@ Ghost.frozen_scope (fun load ->
      let result = load () in
      assert (result === value);
      result) *)
  in
  Atomic.get channel
(*@ Ghost.scope (fun step ->
    let token = Receive.bind () in
    let flag = Receive.access token channel payload published value in
    unfold contents channel published flag;
    let result = step () in
    fold contents channel published flag;
    Receive.commit token channel payload published value result;
    result) *)
(*@ manual *)
(*@ result = atomic receive [published : Ghost.t set] [value : int] channel payload
    requires Value.covered published payload value
    ensures Value.visible Ghost.self payload value
    atomic requires contents channel published flag
    atomic ensures contents channel published flag && result === flag *)

let client (channel : int Atomic.t) (payload : cell) =
  let _ =
    receive channel payload
    (*@ Ghost.scope (fun call -> let result = call (published, value) in result) *)
  in
  payload.value
(*@ Ghost.frozen_scope (fun load -> let result = load () in result) *)
(*@ manual *)
(*@ result = client [published : Ghost.t set] channel payload
    requires contents channel published flag && Value.covered published payload value
    ensures contents channel published flag && result === value *)
