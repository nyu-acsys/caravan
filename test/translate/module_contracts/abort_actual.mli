type t

(*@ predicate counter (x : t) (n [@implicit] : int) *)
(*@ predicate ticket (x : t) (n : int) *)
val read : t -> int
(*@ result = atomic read x
    requires ticket x 7 ensures ticket x 7
    atomic requires counter x n atomic ensures counter x n && result = n *)
