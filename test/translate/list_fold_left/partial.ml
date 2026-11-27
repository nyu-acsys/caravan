let partial values =
  let fold = List.fold_left (fun accumulator _value -> accumulator) 0 in
  fold values
