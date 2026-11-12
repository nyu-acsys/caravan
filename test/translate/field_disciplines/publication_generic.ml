module type Storage = sig
  type 'a t = { mutable item : 'a [@caravan.frozen] }
end

module Generic (Storage : Storage) = struct
  let allocate item : 'a Storage.t = { item }
  (*@ result = allocate item ensures own ~writer:Ghost.self result.item item *)

  let create item = allocate item
  (*@ Ghost.scope (fun step ->
      let cell = step () in
      Item.freeze cell;
      cell) *)
  (*@ manual *)
  (*@ result = create item ensures Item.visible Ghost.self result item *)

  let publish (payload : 'a Storage.t) = Atomic.make 0
  (*@ Ghost.State.release_scope (fun publish () ->
      let published = Item.release payload in
      let channel = publish published in
      (channel, published)) *)
  (*@ Ghost.returns (fun result published -> published) *)
  (*@ manual *)
  (*@ channel, [published : Ghost.t set] = publish payload
      requires Item.visible Ghost.self payload item
      ensures Item.visible Ghost.self payload item
           && Item.covered published payload item
           && own ~release:published channel 0 *)

  let receive (channel : int Atomic.t) (payload : 'a Storage.t) =
    let _ =
      Atomic.get channel
      (*@ Ghost.State.acquire_scope (fun acquire () ->
        let flag = acquire published in
        Item.observe payload published;
        (flag, ())) *)
    in
    payload.item
  (*@ Ghost.frozen_scope (fun load -> let result = load () in result) *)
  (*@ manual *)
  (*@ result = receive [published : Ghost.t set] channel payload
      requires own ~release:published channel 0 && Item.covered published payload item
      ensures own ~release:published channel 0 && Item.visible Ghost.self payload item
           && result === item *)

  let client item =
    let payload = create item in
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
  (*@ result = client item ensures result === item *)
end

module Actual = struct
  type 'a t = { mutable item : 'a [@caravan.frozen] }
end

module Instance = Generic (Actual)

let clients () =
  assert (Instance.client 17 = 17);
  assert (Instance.client true)
