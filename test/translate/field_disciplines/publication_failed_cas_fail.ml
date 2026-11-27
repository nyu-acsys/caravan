type cell = { mutable value : int [@caravan.frozen] }

let failed_cas (channel : int Atomic.t) (payload : cell) =
  Atomic.compare_and_set channel 1 2
(*@ Ghost.State.release_scope (fun publish () ->
    let published = Value.release payload in
    let result = publish published in
    (result, published)) *)
(*@ Ghost.returns (fun result published -> published) *)
(*@ manual *)
(*@ result, [published : Ghost.t set] = failed_cas channel payload
    requires own channel 0 && Value.visible Ghost.self payload value
    ensures own ~release:published channel 0 && result === false *)
