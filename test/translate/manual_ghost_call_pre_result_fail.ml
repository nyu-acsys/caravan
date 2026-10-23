let invalid (value : int) = value
(*@ Ghost.returns (fun result () -> result) *)
(*@ manual *)
(*@ result, [copy : int] = invalid value requires copy = value ensures copy = result *)
