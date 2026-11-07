module type View = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  val read : t -> int
  (*@ result = read x
      requires counter x state && state >= 0
      ensures counter x state && result >= 0 *)
end

module Make (Cell : View) = struct
  let read x = Cell.read x
  (*@ result = read x
      requires Cell.counter x state && state >= 0
      ensures Cell.counter x state && result = state *)
end

module Client = Make (Actual.First)
