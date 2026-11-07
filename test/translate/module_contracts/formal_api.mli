module type Defined = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) = false *)
  val read : t -> int
  (*@ result = read x requires counter x n ensures counter x n && result = n *)
end
