let choose flag (left : int) (right : int) =
  if flag then left (*@ Ghost.returns (fun result () -> result) *) else right
(*@ manual *)
(*@ result, [copy : int] = choose flag left right
    ensures result = copy *)
