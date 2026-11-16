let identity (value : int) = value
(*@ result = identity value
    opens { Ghost.self }
    ensures result = value *)
