type t

(*@ predicate holds (cell : t) (value [@implicit] : int) *)
val read : t -> int
(*@ result = atomic read cell
    atomic requires holds cell value
    atomic ensures holds cell value && result === value *)
