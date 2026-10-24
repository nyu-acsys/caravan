type integer = bool

let identity (value : integer) = value
(*@ result = identity value ensures result = value *)
