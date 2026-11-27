let dynamic choose values =
  List.fold_left
    (if choose then fun accumulator _value -> accumulator
     else fun accumulator _value -> accumulator)
    0 values
