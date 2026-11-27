type cell = { mutable value : int [@caravan.frozen] }

let write (channel : int Atomic.t) = Atomic.set channel 1
(*@ Ghost.acquire_scope (fun acquire ->
    let result = acquire published in
    result) *)
(*@ manual *)
(*@ write [published : Ghost.t set] channel
    requires own ~release:published channel previous
    ensures own ~release:published channel 1 *)
