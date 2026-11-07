module Checked : sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  (*@ predicate ticket (x : t) (n : int) *)
  val read : t -> int
  (*@ result = atomic read x
      atomic requires counter x n && ticket x 7
      atomic ensures counter x n && ticket x 7 && result = n *)
end =
  Abort_actual
