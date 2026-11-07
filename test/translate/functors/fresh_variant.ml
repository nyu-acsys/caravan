module type View = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  val read : t -> int
  (*@ result = read x requires counter x state ensures counter x state && result = state *)
end

module Make (Cell : View) = struct
  type t = Wrap of Cell.t
end

module Client = Make (Actual.First)
