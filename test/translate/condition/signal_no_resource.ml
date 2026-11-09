let signal_no_resource condition (cell : int ref) =
  let _ = cell in
  Condition.signal condition
