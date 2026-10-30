let invalid (value : int) = value
(*@ result = invalid value ensures length (to_sequence value) = 0 *)
