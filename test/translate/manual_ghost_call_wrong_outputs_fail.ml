let identity (value : int) = value
(*@ Ghost.returns (fun result () -> (result, result)) *)
(*@ manual *)
(*@ result, [copy : int] = identity value
    ensures result = copy && copy = value *)
