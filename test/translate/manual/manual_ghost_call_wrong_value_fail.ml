let identity (value : int) = value
(*@ Ghost.returns (fun result () -> result + 1) *)
(*@ manual *)
(*@ result, [copy : int] = identity value
    ensures result = copy && copy = value *)
