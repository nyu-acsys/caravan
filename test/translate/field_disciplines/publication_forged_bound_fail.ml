type cell = { mutable value : int [@caravan.frozen] }

let preserve (channel : int Atomic.t) = channel
(*@ result = preserve [published : Ghost.t set] channel
    requires own channel 0
    ensures own ~release:published result 0 *)
