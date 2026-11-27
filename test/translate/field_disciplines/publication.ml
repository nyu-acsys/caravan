type cell = { mutable value : int [@caravan.frozen] }

let allocate value = { value }
(*@ result = allocate value ensures own ~writer:Ghost.self result.value value *)

let create value = allocate value
(*@ Ghost.scope (fun step ->
    let cell = step () in
    Value.freeze cell;
    cell) *)
(*@ manual *)
(*@ result = create value ensures Value.visible Ghost.self result value *)

let publish (payload : cell) = Atomic.make 0
(*@ Ghost.State.release_scope (fun publish () ->
    let published = Value.release payload in
    let channel = publish published in
    (channel, published)) *)
(*@ Ghost.returns (fun result published -> published) *)
(*@ manual *)
(*@ channel, [published : Ghost.t set] = publish payload
    requires Value.visible Ghost.self payload value
    ensures Value.visible Ghost.self payload value
         && Value.covered published payload value
         && own ~release:published channel 0 *)

let receive (channel : int Atomic.t) (payload : cell) =
  let _ =
    Atomic.get channel
    (*@ Ghost.acquire_scope (fun acquire ->
      let flag = acquire published in
      Value.observe payload published;
      flag) *)
  in
  payload.value
(*@ Ghost.frozen_scope (fun load ->
    let result = load () in
    result) *)
(*@ manual *)
(*@ result = receive [published : Ghost.t set] channel payload
    requires own ~release:published channel 0 && Value.covered published payload value
    ensures own ~release:published channel 0 && Value.visible Ghost.self payload value
         && result === value *)

let client value =
  let payload = create value in
  let channel =
    publish payload
    (*@ Ghost.State.scope (fun call () ->
      let (channel, published) = call () in
      (channel, published)) *)
  in
  receive channel payload
(*@ Ghost.State.scope (fun call (published : Ghost.t set) ->
    let result = call published in
    (result, published)) *)
(*@ manual *)
(*@ result = client value ensures result === value *)

let publish_set (channel : int Atomic.t) (payload : cell) = Atomic.set channel 1
(*@ Ghost.State.release_scope (fun publish () ->
    let published = Value.release payload in
    let result = publish published in
    (result, published)) *)
(*@ Ghost.returns (fun result published -> published) *)
(*@ manual *)
(*@ result, [published : Ghost.t set] = publish_set channel payload
    requires own channel 0 && Value.visible Ghost.self payload value
    ensures own ~release:published channel 1
         && Value.covered published payload value *)

let publish_exchange (channel : int Atomic.t) (payload : cell) = Atomic.exchange channel 1
(*@ Ghost.State.release_scope (fun publish () ->
    let published = Value.release payload in
    let result = publish published in
    (result, published)) *)
(*@ Ghost.returns (fun result published -> published) *)
(*@ manual *)
(*@ result, [published : Ghost.t set] = publish_exchange channel payload
    requires own channel 0 && Value.visible Ghost.self payload value
    ensures own ~release:published channel 1
         && Value.covered published payload value && result === 0 *)

let publish_cas (channel : int Atomic.t) (payload : cell) =
  Atomic.compare_and_set channel 0 1
(*@ Ghost.State.release_scope (fun publish () ->
    let published = Value.release payload in
    let result = publish published in
    (result, published)) *)
(*@ Ghost.returns (fun result published -> published) *)
(*@ manual *)
(*@ result, [published : Ghost.t set] = publish_cas channel payload
    requires own channel 0 && Value.visible Ghost.self payload value
    ensures own ~release:published channel 1
         && Value.covered published payload value && result === true *)

let publish_fetch_add (channel : int Atomic.t) (payload : cell) =
  Atomic.fetch_and_add channel 1
(*@ Ghost.State.release_scope (fun publish () ->
    let published = Value.release payload in
    let result = publish published in
    (result, published)) *)
(*@ Ghost.returns (fun result published -> published) *)
(*@ manual *)
(*@ result, [published : Ghost.t set] = publish_fetch_add channel payload
    requires own channel 0 && Value.visible Ghost.self payload value
    ensures own ~release:published channel 1
         && Value.covered published payload value && result === 0 *)

let publish_incr (channel : int Atomic.t) (payload : cell) = Atomic.incr channel
(*@ Ghost.State.release_scope (fun publish () ->
    let published = Value.release payload in
    let result = publish published in
    (result, published)) *)
(*@ Ghost.returns (fun result published -> published) *)
(*@ manual *)
(*@ result, [published : Ghost.t set] = publish_incr channel payload
    requires own channel 0 && Value.visible Ghost.self payload value
    ensures own ~release:published channel 1
         && Value.covered published payload value *)

let publish_decr (channel : int Atomic.t) (payload : cell) = Atomic.decr channel
(*@ Ghost.State.release_scope (fun publish () ->
    let published = Value.release payload in
    let result = publish published in
    (result, published)) *)
(*@ Ghost.returns (fun result published -> published) *)
(*@ manual *)
(*@ result, [published : Ghost.t set] = publish_decr channel payload
    requires own channel 1 && Value.visible Ghost.self payload value
    ensures own ~release:published channel 0
         && Value.covered published payload value *)

let overwrite (channel : int Atomic.t) = Atomic.set channel 5
(*@ overwrite [published : Ghost.t set] channel
    requires own ~release:published channel 0
    ensures own ~release:published channel 5 *)

let receive_half (channel : int Atomic.t) (payload : cell) =
  let _ =
    Atomic.get channel
    (*@ Ghost.acquire_scope (fun acquire ->
      let flag = acquire published in
      Value.observe payload published;
      flag) *)
  in
  payload.value
(*@ Ghost.frozen_scope (fun load -> let result = load () in result) *)
(*@ manual *)
(*@ result = receive_half [published : Ghost.t set] channel payload
    requires own ~fraction:Permission.half ~release:published channel 0
         && Value.covered published payload value
    ensures own ~release:published ~fraction:Permission.half channel 0
         && result === value *)

let make_plain value = Atomic.make value
(*@ Ghost.scope (fun make ->
    let result = make () in
    result) *)
(*@ manual *)
(*@ result = make_plain value ensures own result value *)

let publish_typed (payload : cell) initial = Atomic.make initial
(*@ Ghost.State.release_scope (fun publish () ->
    let published = Value.release payload in
    let channel = publish published in
    (channel, published)) *)
(*@ Ghost.returns (fun result published -> published) *)
(*@ manual *)
(*@ channel, [published : Ghost.t set] = publish_typed payload initial
    requires Value.visible Ghost.self payload value
    ensures own ~release:published channel initial && Value.covered published payload value *)

let receive_typed (channel : 'a Atomic.t) (payload : cell) = Atomic.get channel
(*@ Ghost.acquire_scope (fun acquire ->
    let result = acquire published in
    Value.observe payload published;
    result) *)
(*@ manual *)
(*@ result = receive_typed [published : Ghost.t set] channel payload
    requires own ~release:published channel initial && Value.covered published payload value
    ensures own ~release:published channel initial && Value.visible Ghost.self payload value
         && result === initial *)

let publish_plain (channel : int Atomic.t) (payload : cell) = Atomic.set channel 1
(*@ Ghost.release_scope (fun publish ->
    let published = Value.release payload in
    let result = publish published in
    result) *)
(*@ manual *)
(*@ publish_plain channel payload
    requires own ~release:prior channel 0 && Value.visible Ghost.self payload value
    ensures own ~release:prior channel 1 *)

let receive_failed_cas (channel : int Atomic.t) (payload : cell) =
  let _ =
    Atomic.compare_and_set channel 1 2
    (*@ Ghost.acquire_scope (fun acquire ->
      let result = acquire published in
      assert (result === false);
      Value.observe payload published;
      result) *)
  in
  payload.value
(*@ Ghost.frozen_scope (fun load -> let result = load () in result) *)
(*@ manual *)
(*@ result = receive_failed_cas [published : Ghost.t set] channel payload
    requires own ~fraction:Permission.half ~release:published channel 0
         && Value.covered published payload value
    ensures own ~fraction:Permission.half ~release:published channel 0
         && result === value *)
