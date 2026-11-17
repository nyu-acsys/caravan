type cell = { mutable value : int }

let reset (c : cell) = c.value <- 0
(*@ reset [cells : cell list] [k : integer] c
    requires cells_seg cells 0 0 && cells_located cells 0 k c
    ensures cells_seg cells 0 0 *)
