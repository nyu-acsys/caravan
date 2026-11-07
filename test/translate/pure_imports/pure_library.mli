type t

val identity : 'a -> 'a
(*@ result = identity value
    pure
    ensures result === value *)

val bounded : int -> int
(*@ result = bounded value
    pure
    requires value >= 0
    ensures result === value
    ensures result >= 0 *)

val twice : 'a -> 'a
(*@ result = twice value
    pure
    ensures result === identity (identity value) *)
