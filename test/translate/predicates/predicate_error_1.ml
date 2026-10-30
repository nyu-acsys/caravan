type counter = { mutable count : int }

let f (c : counter) = c.count
(*@ v = f c
    requires own c.count n *)
(*@ unfold valid c n *)
