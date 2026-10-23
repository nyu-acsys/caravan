let identity (value : int) = value
(*@ manual *)
(*@ result, [copy : int] = identity value
    ensures result = copy && copy = value *)
