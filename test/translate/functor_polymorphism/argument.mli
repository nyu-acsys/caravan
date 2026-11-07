val id : 'a -> 'a
(*@ result = id value ensures result === value *)

val swap : 'a -> 'b -> 'b * 'a
(*@ result = swap left right ensures result === (right, left) *)
