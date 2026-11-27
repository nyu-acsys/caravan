type cell = { mutable value : int [@caravan.frozen] }

let read (channel : int Atomic.t) (payload : cell) = Atomic.get channel
(*@ Ghost.acquire_scope (fun acquire ->
    let result = acquire published in
    result) *)
(*@ manual *)
(*@ result = read [published : Ghost.t set] channel payload
    requires own channel 0 && Value.covered published payload value
    ensures own channel 0 && result === 0 *)
