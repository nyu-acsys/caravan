type counter = { mutable count : int }

let get c = c.count
(*@ v = get c
    requires c.count > 0 *)
