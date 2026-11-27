type cell = { mutable value : int [@caravan.frozen] }

let publish (payload : cell) = Atomic.make 0
(*@ Ghost.State.release_scope (fun publish () ->
    let published = Value.release payload in
    let channel = publish published in
    (channel, published)) *)
(*@ Ghost.returns (fun result published -> published) *)
(*@ manual *)
(*@ result, [published : Ghost.t set] = publish payload
    requires Value.visible other payload value
    ensures Value.covered published payload value && own ~release:published result 0 *)
