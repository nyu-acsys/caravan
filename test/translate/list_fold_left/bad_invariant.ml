let wrong (values : int list) =
  List.fold_left (fun accumulator _value -> accumulator) 0 values
