let read (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun step ->
    let result = step () in
    result) *)
(*@ Ghost.returns (fun result () -> (result, result)) *)
(*@ manual *)
(*@ result, [stamp : int * int] = read cell
    requires own cell value
    ensures own cell value && result = value && stamp = (value, value)
    raises Exit -> false *)

let check cell = read cell
(*@ Ghost.scope (fun invoke ->
    let (result, (first, second)) = invoke () in
    assert (first = result && second = result);
    result) *)
(*@ manual *)
(*@ result = check cell
    requires own cell value
    ensures own cell value && result = value
    raises Exit -> false *)
