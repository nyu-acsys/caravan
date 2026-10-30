let to_sequence (value : int) = value
let identity (value : int) = value
(*@ result = identity value ensures to_sequence result = value *)
