let read (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun step ->
    let token = Read.bind () in
    let value = Other.access token cell in
    unfold contents cell value;
    let result = step () in
    fold contents cell value;
    Read.commit token cell result;
    result)
*)
(*@ manual *)
(*@ result = atomic read cell
    atomic requires contents cell value
    atomic ensures contents cell value && result = value *)

let other (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun step ->
    let token = Other.bind () in
    let value = Other.access token cell in
    unfold contents cell value;
    let result = step () in
    fold contents cell value;
    Other.commit token cell result;
    result)
*)
(*@ manual *)
(*@ result = atomic other cell
    atomic requires contents cell value
    atomic ensures contents cell value && result = value *)
