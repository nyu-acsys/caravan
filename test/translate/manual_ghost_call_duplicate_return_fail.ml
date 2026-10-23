let invalid (value : int) = value
(*@ Ghost.returns (fun result () -> result) *)
(*@ Ghost.returns (fun result () -> result) *)
(*@ manual *)
(*@ result, [copy : int] = invalid value ensures copy = result *)
