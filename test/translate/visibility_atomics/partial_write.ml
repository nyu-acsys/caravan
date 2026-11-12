type unused = { mutable data : int [@caravan.frozen] }

let write (cell : int Atomic.t) = Atomic.set cell 1
(*@ write cell
    requires own ~fraction:Permission.half cell 0
    ensures own ~fraction:Permission.half cell 1 *)
