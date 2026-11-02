val id : 'a -> 'a
(*@ result = id value pure ensures result === value *)

val integer : int -> int
(*@ result = integer value ensures result === value *)

val boolean : bool -> bool
(*@ result = boolean value ensures result === value *)
