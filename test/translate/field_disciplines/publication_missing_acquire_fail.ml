type cell = { mutable value : int [@caravan.frozen] }

let read (channel : int Atomic.t) (payload : cell) = payload.value
(*@ Ghost.frozen_scope (fun load ->
    Value.observe payload published;
    let result = load () in
    result) *)
(*@ manual *)
(*@ result = read [published : Ghost.t set] channel payload
    requires own ~release:published channel 0 && Value.covered published payload value
    ensures result === value *)
