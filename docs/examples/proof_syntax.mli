(*@ predicate stored (cell : int ref) (value : int) *)

val make : int -> int ref
(*@ cell = make value ensures stored cell value *)
