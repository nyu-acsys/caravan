let identity (value : int) = value
(*@ result = identity [expected : int] value
    requires expected = value
    ensures result = expected *)

let use_identity (value : int) = identity value
(*@ Ghost.scope (fun invoke ->
    let result = invoke () in
    result) *)
(*@ manual *)
(*@ result = use_identity value ensures result = value *)
