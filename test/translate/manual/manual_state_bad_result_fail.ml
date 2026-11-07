let read (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.State.scope (fun step () ->
    let result = step () in
    (result + 1, result)) *)
(*@ manual *)
(*@ result = read cell
    requires own cell value
    ensures own cell value && result = value *)
