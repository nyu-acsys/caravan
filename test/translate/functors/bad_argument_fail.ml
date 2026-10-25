module type View = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  val read : t -> int
  (*@ result = read x requires counter x state ensures counter x state && result = state *)
end

module Make (Cell : View) = struct
  let read x = Cell.read x
  (*@ result = read x requires Cell.counter x state ensures Cell.counter x state && result = state *)
end

module Client = Make (Actual.Strong_First)
